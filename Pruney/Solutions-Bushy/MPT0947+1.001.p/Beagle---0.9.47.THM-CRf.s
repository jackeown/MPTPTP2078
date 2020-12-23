%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0947+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:07 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 107 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > v3_ordinal1 > v1_relat_1 > #nlpp > k1_wellord2 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r4_wellord1(A,k1_wellord2(B))
                    & r4_wellord1(A,k1_wellord2(C)) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord2)).

tff(f_26,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(f_35,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(c_10,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k1_wellord2(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    r4_wellord1('#skF_1',k1_wellord2('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [B_20,A_21] :
      ( r4_wellord1(B_20,A_21)
      | ~ r4_wellord1(A_21,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,
    ( r4_wellord1(k1_wellord2('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k1_wellord2('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_22])).

tff(c_32,plain,(
    r4_wellord1(k1_wellord2('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_26])).

tff(c_16,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    r4_wellord1('#skF_1',k1_wellord2('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_24,C_25,B_26] :
      ( r4_wellord1(A_24,C_25)
      | ~ r4_wellord1(B_26,C_25)
      | ~ r4_wellord1(A_24,B_26)
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ! [A_24] :
      ( r4_wellord1(A_24,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_24,'#skF_1')
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_65,plain,(
    ! [A_27] :
      ( r4_wellord1(A_27,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_27,'#skF_1')
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_50])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( B_4 = A_2
      | ~ r4_wellord1(k1_wellord2(A_2),k1_wellord2(B_4))
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v3_ordinal1('#skF_3')
      | ~ v3_ordinal1(A_2)
      | ~ r4_wellord1(k1_wellord2(A_2),'#skF_1')
      | ~ v1_relat_1(k1_wellord2(A_2)) ) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_83,plain,(
    ! [A_28] :
      ( A_28 = '#skF_3'
      | ~ v3_ordinal1(A_28)
      | ~ r4_wellord1(k1_wellord2(A_28),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16,c_71])).

tff(c_86,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_83])).

tff(c_92,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_92])).

%------------------------------------------------------------------------------
