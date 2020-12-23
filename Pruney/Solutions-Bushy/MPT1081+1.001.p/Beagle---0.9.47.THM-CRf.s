%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1081+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:22 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  84 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 161 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(m1_funct_2,type,(
    m1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => m1_funct_2(k1_tarski(C),A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_24,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ~ m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1('#skF_1'(A_33,B_34,C_35),C_35)
      | m1_funct_2(C_35,A_33,B_34)
      | v1_xboole_0(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_7,A_19] :
      ( A_7 = A_19
      | v1_xboole_0(k1_tarski(A_7))
      | ~ m1_subset_1(A_19,k1_tarski(A_7)) ) ),
    inference(resolution,[status(thm)],[c_43,c_12])).

tff(c_50,plain,(
    ! [A_7,A_19] :
      ( A_7 = A_19
      | ~ m1_subset_1(A_19,k1_tarski(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_47])).

tff(c_76,plain,(
    ! [A_33,B_34,A_7] :
      ( '#skF_1'(A_33,B_34,k1_tarski(A_7)) = A_7
      | m1_funct_2(k1_tarski(A_7),A_33,B_34)
      | v1_xboole_0(k1_tarski(A_7)) ) ),
    inference(resolution,[status(thm)],[c_70,c_50])).

tff(c_81,plain,(
    ! [A_36,B_37,A_38] :
      ( '#skF_1'(A_36,B_37,k1_tarski(A_38)) = A_38
      | m1_funct_2(k1_tarski(A_38),A_36,B_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_76])).

tff(c_85,plain,(
    '#skF_1'('#skF_4','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_81,c_28])).

tff(c_32,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_335,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ m1_subset_1('#skF_1'(A_92,B_93,C_94),k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2('#skF_1'(A_92,B_93,C_94),A_92,B_93)
      | ~ v1_funct_1('#skF_1'(A_92,B_93,C_94))
      | m1_funct_2(C_94,A_92,B_93)
      | v1_xboole_0(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_348,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_1'('#skF_4','#skF_5',k1_tarski('#skF_6')),'#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_1'('#skF_4','#skF_5',k1_tarski('#skF_6')))
    | m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_335])).

tff(c_357,plain,
    ( m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_85,c_32,c_85,c_30,c_348])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_28,c_357])).

%------------------------------------------------------------------------------
