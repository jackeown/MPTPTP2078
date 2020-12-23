%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0718+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:45 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 124 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_16,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_relat_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_funct_1(A_1,'#skF_1'(A_1)))
      | v2_relat_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_116,plain,(
    ! [B_35,C_36,A_37] :
      ( r2_hidden(k1_funct_1(B_35,C_36),k1_funct_1(A_37,C_36))
      | ~ r2_hidden(C_36,k1_relat_1(B_35))
      | ~ v5_funct_1(B_35,A_37)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( ~ v1_xboole_0(B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_127,plain,(
    ! [A_40,C_41,B_42] :
      ( ~ v1_xboole_0(k1_funct_1(A_40,C_41))
      | ~ r2_hidden(C_41,k1_relat_1(B_42))
      | ~ v5_funct_1(B_42,A_40)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_116,c_14])).

tff(c_131,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43),k1_relat_1(B_44))
      | ~ v5_funct_1(B_44,A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | v2_relat_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_127])).

tff(c_137,plain,(
    ! [A_43] :
      ( ~ r2_hidden('#skF_1'(A_43),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_43)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | v2_relat_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_131])).

tff(c_142,plain,(
    ! [A_46] :
      ( ~ r2_hidden('#skF_1'(A_46),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_46)
      | v2_relat_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_137])).

tff(c_146,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_149,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_146])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_149])).

%------------------------------------------------------------------------------
