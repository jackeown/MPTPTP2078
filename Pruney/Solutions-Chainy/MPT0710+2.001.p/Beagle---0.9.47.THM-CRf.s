%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:29 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 762 expanded)
%              Number of leaves         :   24 ( 260 expanded)
%              Depth                    :   20
%              Number of atoms          :  322 (2541 expanded)
%              Number of equality atoms :  117 ( 752 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(C,k1_relat_1(B)) )
               => ( k7_relat_1(A,C) = k7_relat_1(B,C)
                <=> ! [D] :
                      ( r2_hidden(D,C)
                     => k1_funct_1(A,D) = k1_funct_1(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( ( k1_relat_1(B) = k3_xboole_0(k1_relat_1(C),A)
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) )
           => B = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_32,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ! [B_46,A_47] :
      ( k1_relat_1(k7_relat_1(B_46,A_47)) = A_47
      | ~ r1_tarski(A_47,k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_74,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_68])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k3_xboole_0(k1_relat_1(B_4),A_3) = k1_relat_1(k7_relat_1(B_4,A_3))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_funct_1(k7_relat_1(A_7,B_8))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_65,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_71,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_65])).

tff(c_81,plain,(
    ! [A_3] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_3)) = k3_xboole_0('#skF_4',A_3)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_723,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_727,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_723])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_727])).

tff(c_733,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_734,plain,(
    ! [A_122] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_122)) = k3_xboole_0('#skF_4',A_122) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k1_relat_1(k7_relat_1(B_6,A_5)) = A_5
      | ~ r1_tarski(A_5,k1_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_819,plain,(
    ! [A_132,A_133] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_132),A_133)) = A_133
      | ~ r1_tarski(A_133,k3_xboole_0('#skF_4',A_132))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_6])).

tff(c_743,plain,(
    ! [A_122,A_3] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_122),A_3)) = k3_xboole_0(k3_xboole_0('#skF_4',A_122),A_3)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_4])).

tff(c_861,plain,(
    ! [A_136,A_137] :
      ( k3_xboole_0(k3_xboole_0('#skF_4',A_136),A_137) = A_137
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_136))
      | ~ r1_tarski(A_137,k3_xboole_0('#skF_4',A_136))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_743])).

tff(c_864,plain,(
    ! [B_8,A_137] :
      ( k3_xboole_0(k3_xboole_0('#skF_4',B_8),A_137) = A_137
      | ~ r1_tarski(A_137,k3_xboole_0('#skF_4',B_8))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),B_8))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_861])).

tff(c_867,plain,(
    ! [B_8,A_137] :
      ( k3_xboole_0(k3_xboole_0('#skF_4',B_8),A_137) = A_137
      | ~ r1_tarski(A_137,k3_xboole_0('#skF_4',B_8))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),B_8))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_864])).

tff(c_868,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_871,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_868])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_871])).

tff(c_877,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_878,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden('#skF_1'(A_138,B_139,C_140),k1_relat_1(B_139))
      | k7_relat_1(C_140,A_138) = B_139
      | k3_xboole_0(k1_relat_1(C_140),A_138) != k1_relat_1(B_139)
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_902,plain,(
    ! [A_138,C_140] :
      ( r2_hidden('#skF_1'(A_138,k7_relat_1('#skF_3','#skF_4'),C_140),'#skF_4')
      | k7_relat_1(C_140,A_138) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_140),A_138) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_878])).

tff(c_908,plain,(
    ! [A_138,C_140] :
      ( r2_hidden('#skF_1'(A_138,k7_relat_1('#skF_3','#skF_4'),C_140),'#skF_4')
      | k7_relat_1(C_140,A_138) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_140),A_138) != '#skF_4'
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_71,c_902])).

tff(c_1166,plain,(
    ! [A_138,C_140] :
      ( r2_hidden('#skF_1'(A_138,k7_relat_1('#skF_3','#skF_4'),C_140),'#skF_4')
      | k7_relat_1(C_140,A_138) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_140),A_138) != '#skF_4'
      | ~ v1_funct_1(C_140)
      | ~ v1_relat_1(C_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_908])).

tff(c_1167,plain,(
    ! [A_172,C_173] :
      ( r2_hidden('#skF_1'(A_172,k7_relat_1('#skF_3','#skF_4'),C_173),'#skF_4')
      | k7_relat_1(C_173,A_172) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_173),A_172) != '#skF_4'
      | ~ v1_funct_1(C_173)
      | ~ v1_relat_1(C_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_908])).

tff(c_127,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_130,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_130])).

tff(c_136,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_174,plain,(
    ! [A_53] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_53)) = k3_xboole_0('#skF_4',A_53) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_255,plain,(
    ! [A_64,A_65] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_64),A_65)) = A_65
      | ~ r1_tarski(A_65,k3_xboole_0('#skF_4',A_64))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_6])).

tff(c_183,plain,(
    ! [A_53,A_3] :
      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_53),A_3)) = k3_xboole_0(k3_xboole_0('#skF_4',A_53),A_3)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_4])).

tff(c_325,plain,(
    ! [A_73,A_74] :
      ( k3_xboole_0(k3_xboole_0('#skF_4',A_73),A_74) = A_74
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_73))
      | ~ r1_tarski(A_74,k3_xboole_0('#skF_4',A_73))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_183])).

tff(c_328,plain,(
    ! [B_8,A_74] :
      ( k3_xboole_0(k3_xboole_0('#skF_4',B_8),A_74) = A_74
      | ~ r1_tarski(A_74,k3_xboole_0('#skF_4',B_8))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),B_8))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_325])).

tff(c_331,plain,(
    ! [B_8,A_74] :
      ( k3_xboole_0(k3_xboole_0('#skF_4',B_8),A_74) = A_74
      | ~ r1_tarski(A_74,k3_xboole_0('#skF_4',B_8))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),B_8))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_328])).

tff(c_339,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_342,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_339])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_342])).

tff(c_348,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_293,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),k1_relat_1(B_69))
      | k7_relat_1(C_70,A_68) = B_69
      | k3_xboole_0(k1_relat_1(C_70),A_68) != k1_relat_1(B_69)
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70)
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_317,plain,(
    ! [A_68,C_70] :
      ( r2_hidden('#skF_1'(A_68,k7_relat_1('#skF_3','#skF_4'),C_70),'#skF_4')
      | k7_relat_1(C_70,A_68) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_70),A_68) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_293])).

tff(c_323,plain,(
    ! [A_68,C_70] :
      ( r2_hidden('#skF_1'(A_68,k7_relat_1('#skF_3','#skF_4'),C_70),'#skF_4')
      | k7_relat_1(C_70,A_68) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_70),A_68) != '#skF_4'
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_71,c_317])).

tff(c_581,plain,(
    ! [A_68,C_70] :
      ( r2_hidden('#skF_1'(A_68,k7_relat_1('#skF_3','#skF_4'),C_70),'#skF_4')
      | k7_relat_1(C_70,A_68) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_70),A_68) != '#skF_4'
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_323])).

tff(c_582,plain,(
    ! [A_102,C_103] :
      ( r2_hidden('#skF_1'(A_102,k7_relat_1('#skF_3','#skF_4'),C_103),'#skF_4')
      | k7_relat_1(C_103,A_102) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_103),A_102) != '#skF_4'
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_323])).

tff(c_36,plain,(
    ! [D_37] :
      ( k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5')
      | k1_funct_1('#skF_2',D_37) = k1_funct_1('#skF_3',D_37)
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_137,plain,(
    k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    ! [D_37] :
      ( r2_hidden('#skF_5','#skF_4')
      | k1_funct_1('#skF_2',D_37) = k1_funct_1('#skF_3',D_37)
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_95,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    ! [D_37] :
      ( k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4')
      | k1_funct_1('#skF_2',D_37) = k1_funct_1('#skF_3',D_37)
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_154,plain,(
    ! [D_51] :
      ( k1_funct_1('#skF_2',D_51) = k1_funct_1('#skF_3',D_51)
      | ~ r2_hidden(D_51,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_40])).

tff(c_157,plain,(
    k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_154])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_157])).

tff(c_162,plain,(
    ! [D_37] :
      ( k1_funct_1('#skF_2',D_37) = k1_funct_1('#skF_3',D_37)
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_667,plain,(
    ! [A_114,C_115] :
      ( k1_funct_1('#skF_2','#skF_1'(A_114,k7_relat_1('#skF_3','#skF_4'),C_115)) = k1_funct_1('#skF_3','#skF_1'(A_114,k7_relat_1('#skF_3','#skF_4'),C_115))
      | k7_relat_1(C_115,A_114) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_115),A_114) != '#skF_4'
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_582,c_162])).

tff(c_16,plain,(
    ! [C_18,B_17,A_16] :
      ( k1_funct_1(k7_relat_1(C_18,B_17),A_16) = k1_funct_1(C_18,A_16)
      | ~ r2_hidden(A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_353,plain,(
    ! [C_79,A_80,B_81] :
      ( k1_funct_1(C_79,'#skF_1'(A_80,B_81,C_79)) != k1_funct_1(B_81,'#skF_1'(A_80,B_81,C_79))
      | k7_relat_1(C_79,A_80) = B_81
      | k3_xboole_0(k1_relat_1(C_79),A_80) != k1_relat_1(B_81)
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_359,plain,(
    ! [C_79,A_80,C_18,B_17] :
      ( k1_funct_1(C_79,'#skF_1'(A_80,k7_relat_1(C_18,B_17),C_79)) != k1_funct_1(C_18,'#skF_1'(A_80,k7_relat_1(C_18,B_17),C_79))
      | k7_relat_1(C_79,A_80) = k7_relat_1(C_18,B_17)
      | k3_xboole_0(k1_relat_1(C_79),A_80) != k1_relat_1(k7_relat_1(C_18,B_17))
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79)
      | ~ v1_funct_1(k7_relat_1(C_18,B_17))
      | ~ v1_relat_1(k7_relat_1(C_18,B_17))
      | ~ r2_hidden('#skF_1'(A_80,k7_relat_1(C_18,B_17),C_79),B_17)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_353])).

tff(c_673,plain,(
    ! [A_114] :
      ( k3_xboole_0(k1_relat_1('#skF_2'),A_114) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_114,k7_relat_1('#skF_3','#skF_4'),'#skF_2'),'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k7_relat_1('#skF_2',A_114) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_114) != '#skF_4'
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_359])).

tff(c_682,plain,(
    ! [A_116] :
      ( ~ r2_hidden('#skF_1'(A_116,k7_relat_1('#skF_3','#skF_4'),'#skF_2'),'#skF_4')
      | k7_relat_1('#skF_2',A_116) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_116) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_136,c_348,c_71,c_673])).

tff(c_686,plain,(
    ! [A_68] :
      ( k7_relat_1('#skF_2',A_68) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_68) != '#skF_4'
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_581,c_682])).

tff(c_705,plain,(
    ! [A_119] :
      ( k7_relat_1('#skF_2',A_119) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_119) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_686])).

tff(c_709,plain,(
    ! [A_3] :
      ( k7_relat_1('#skF_2',A_3) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_3)) != '#skF_4'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_705])).

tff(c_712,plain,(
    ! [A_120] :
      ( k7_relat_1('#skF_2',A_120) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_120)) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_709])).

tff(c_715,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_712])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_715])).

tff(c_720,plain,(
    ! [D_37] :
      ( k1_funct_1('#skF_2',D_37) = k1_funct_1('#skF_3',D_37)
      | ~ r2_hidden(D_37,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1252,plain,(
    ! [A_184,C_185] :
      ( k1_funct_1('#skF_2','#skF_1'(A_184,k7_relat_1('#skF_3','#skF_4'),C_185)) = k1_funct_1('#skF_3','#skF_1'(A_184,k7_relat_1('#skF_3','#skF_4'),C_185))
      | k7_relat_1(C_185,A_184) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_185),A_184) != '#skF_4'
      | ~ v1_funct_1(C_185)
      | ~ v1_relat_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_1167,c_720])).

tff(c_938,plain,(
    ! [C_149,A_150,B_151] :
      ( k1_funct_1(C_149,'#skF_1'(A_150,B_151,C_149)) != k1_funct_1(B_151,'#skF_1'(A_150,B_151,C_149))
      | k7_relat_1(C_149,A_150) = B_151
      | k3_xboole_0(k1_relat_1(C_149),A_150) != k1_relat_1(B_151)
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149)
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_944,plain,(
    ! [C_18,A_150,B_17,C_149] :
      ( k1_funct_1(C_18,'#skF_1'(A_150,k7_relat_1(C_18,B_17),C_149)) != k1_funct_1(C_149,'#skF_1'(A_150,k7_relat_1(C_18,B_17),C_149))
      | k7_relat_1(C_18,B_17) = k7_relat_1(C_149,A_150)
      | k3_xboole_0(k1_relat_1(C_149),A_150) != k1_relat_1(k7_relat_1(C_18,B_17))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149)
      | ~ v1_funct_1(k7_relat_1(C_18,B_17))
      | ~ v1_relat_1(k7_relat_1(C_18,B_17))
      | ~ r2_hidden('#skF_1'(A_150,k7_relat_1(C_18,B_17),C_149),B_17)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_938])).

tff(c_1258,plain,(
    ! [A_184] :
      ( k3_xboole_0(k1_relat_1('#skF_2'),A_184) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_184,k7_relat_1('#skF_3','#skF_4'),'#skF_2'),'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k7_relat_1('#skF_2',A_184) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_184) != '#skF_4'
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_944])).

tff(c_1267,plain,(
    ! [A_186] :
      ( ~ r2_hidden('#skF_1'(A_186,k7_relat_1('#skF_3','#skF_4'),'#skF_2'),'#skF_4')
      | k7_relat_1('#skF_2',A_186) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_186) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_733,c_877,c_71,c_1258])).

tff(c_1271,plain,(
    ! [A_138] :
      ( k7_relat_1('#skF_2',A_138) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_138) != '#skF_4'
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1166,c_1267])).

tff(c_1290,plain,(
    ! [A_189] :
      ( k7_relat_1('#skF_2',A_189) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_189) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1271])).

tff(c_1294,plain,(
    ! [A_3] :
      ( k7_relat_1('#skF_2',A_3) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_3)) != '#skF_4'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1290])).

tff(c_1297,plain,(
    ! [A_190] :
      ( k7_relat_1('#skF_2',A_190) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_190)) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1294])).

tff(c_1300,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1297])).

tff(c_1304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1300])).

tff(c_1306,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5')
    | k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1377,plain,(
    k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_30])).

tff(c_1305,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1379,plain,(
    ! [C_197,B_198,A_199] :
      ( k1_funct_1(k7_relat_1(C_197,B_198),A_199) = k1_funct_1(C_197,A_199)
      | ~ r2_hidden(A_199,B_198)
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1388,plain,(
    ! [A_199] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_199) = k1_funct_1('#skF_2',A_199)
      | ~ r2_hidden(A_199,'#skF_4')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_1379])).

tff(c_1393,plain,(
    ! [A_200] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_200) = k1_funct_1('#skF_2',A_200)
      | ~ r2_hidden(A_200,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1388])).

tff(c_1399,plain,(
    ! [A_200] :
      ( k1_funct_1('#skF_2',A_200) = k1_funct_1('#skF_3',A_200)
      | ~ r2_hidden(A_200,'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r2_hidden(A_200,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_16])).

tff(c_1413,plain,(
    ! [A_201] :
      ( k1_funct_1('#skF_2',A_201) = k1_funct_1('#skF_3',A_201)
      | ~ r2_hidden(A_201,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_1399])).

tff(c_1416,plain,(
    k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_1305,c_1413])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1377,c_1416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.65  
% 3.97/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.65  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.97/1.65  
% 3.97/1.65  %Foreground sorts:
% 3.97/1.65  
% 3.97/1.65  
% 3.97/1.65  %Background operators:
% 3.97/1.65  
% 3.97/1.65  
% 3.97/1.65  %Foreground operators:
% 3.97/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.97/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.97/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.97/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.97/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.97/1.65  
% 3.97/1.68  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 3.97/1.68  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.97/1.68  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.97/1.68  tff(f_45, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 3.97/1.68  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = k3_xboole_0(k1_relat_1(C), A)) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))) => (B = k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_funct_1)).
% 3.97/1.68  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 3.97/1.68  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4') | k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_52, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 3.97/1.68  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_20, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_62, plain, (![B_46, A_47]: (k1_relat_1(k7_relat_1(B_46, A_47))=A_47 | ~r1_tarski(A_47, k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.68  tff(c_68, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_62])).
% 3.97/1.68  tff(c_74, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_68])).
% 3.97/1.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(k1_relat_1(B_4), A_3)=k1_relat_1(k7_relat_1(B_4, A_3)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.68  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_8, plain, (![A_7, B_8]: (v1_funct_1(k7_relat_1(A_7, B_8)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.97/1.68  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.97/1.68  tff(c_18, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_65, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_62])).
% 3.97/1.68  tff(c_71, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_65])).
% 3.97/1.68  tff(c_81, plain, (![A_3]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_3))=k3_xboole_0('#skF_4', A_3) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 3.97/1.68  tff(c_723, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.97/1.68  tff(c_727, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_723])).
% 3.97/1.68  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_727])).
% 3.97/1.68  tff(c_733, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_81])).
% 3.97/1.68  tff(c_734, plain, (![A_122]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_122))=k3_xboole_0('#skF_4', A_122))), inference(splitRight, [status(thm)], [c_81])).
% 3.97/1.68  tff(c_6, plain, (![B_6, A_5]: (k1_relat_1(k7_relat_1(B_6, A_5))=A_5 | ~r1_tarski(A_5, k1_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.68  tff(c_819, plain, (![A_132, A_133]: (k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_132), A_133))=A_133 | ~r1_tarski(A_133, k3_xboole_0('#skF_4', A_132)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_132)))), inference(superposition, [status(thm), theory('equality')], [c_734, c_6])).
% 3.97/1.68  tff(c_743, plain, (![A_122, A_3]: (k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_122), A_3))=k3_xboole_0(k3_xboole_0('#skF_4', A_122), A_3) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_122)))), inference(superposition, [status(thm), theory('equality')], [c_734, c_4])).
% 3.97/1.68  tff(c_861, plain, (![A_136, A_137]: (k3_xboole_0(k3_xboole_0('#skF_4', A_136), A_137)=A_137 | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_136)) | ~r1_tarski(A_137, k3_xboole_0('#skF_4', A_136)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_136)))), inference(superposition, [status(thm), theory('equality')], [c_819, c_743])).
% 3.97/1.68  tff(c_864, plain, (![B_8, A_137]: (k3_xboole_0(k3_xboole_0('#skF_4', B_8), A_137)=A_137 | ~r1_tarski(A_137, k3_xboole_0('#skF_4', B_8)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), B_8)) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_10, c_861])).
% 3.97/1.68  tff(c_867, plain, (![B_8, A_137]: (k3_xboole_0(k3_xboole_0('#skF_4', B_8), A_137)=A_137 | ~r1_tarski(A_137, k3_xboole_0('#skF_4', B_8)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), B_8)) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_733, c_864])).
% 3.97/1.68  tff(c_868, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_867])).
% 3.97/1.68  tff(c_871, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_868])).
% 3.97/1.68  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_871])).
% 3.97/1.68  tff(c_877, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_867])).
% 3.97/1.68  tff(c_878, plain, (![A_138, B_139, C_140]: (r2_hidden('#skF_1'(A_138, B_139, C_140), k1_relat_1(B_139)) | k7_relat_1(C_140, A_138)=B_139 | k3_xboole_0(k1_relat_1(C_140), A_138)!=k1_relat_1(B_139) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.68  tff(c_902, plain, (![A_138, C_140]: (r2_hidden('#skF_1'(A_138, k7_relat_1('#skF_3', '#skF_4'), C_140), '#skF_4') | k7_relat_1(C_140, A_138)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_140), A_138)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_140) | ~v1_relat_1(C_140) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_878])).
% 3.97/1.68  tff(c_908, plain, (![A_138, C_140]: (r2_hidden('#skF_1'(A_138, k7_relat_1('#skF_3', '#skF_4'), C_140), '#skF_4') | k7_relat_1(C_140, A_138)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_140), A_138)!='#skF_4' | ~v1_funct_1(C_140) | ~v1_relat_1(C_140) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_733, c_71, c_902])).
% 3.97/1.68  tff(c_1166, plain, (![A_138, C_140]: (r2_hidden('#skF_1'(A_138, k7_relat_1('#skF_3', '#skF_4'), C_140), '#skF_4') | k7_relat_1(C_140, A_138)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_140), A_138)!='#skF_4' | ~v1_funct_1(C_140) | ~v1_relat_1(C_140))), inference(demodulation, [status(thm), theory('equality')], [c_877, c_908])).
% 3.97/1.68  tff(c_1167, plain, (![A_172, C_173]: (r2_hidden('#skF_1'(A_172, k7_relat_1('#skF_3', '#skF_4'), C_173), '#skF_4') | k7_relat_1(C_173, A_172)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_173), A_172)!='#skF_4' | ~v1_funct_1(C_173) | ~v1_relat_1(C_173))), inference(demodulation, [status(thm), theory('equality')], [c_877, c_908])).
% 3.97/1.68  tff(c_127, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_81])).
% 3.97/1.68  tff(c_130, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_127])).
% 3.97/1.68  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_130])).
% 3.97/1.68  tff(c_136, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_81])).
% 3.97/1.68  tff(c_174, plain, (![A_53]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_53))=k3_xboole_0('#skF_4', A_53))), inference(splitRight, [status(thm)], [c_81])).
% 3.97/1.68  tff(c_255, plain, (![A_64, A_65]: (k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_64), A_65))=A_65 | ~r1_tarski(A_65, k3_xboole_0('#skF_4', A_64)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_64)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_6])).
% 3.97/1.68  tff(c_183, plain, (![A_53, A_3]: (k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_53), A_3))=k3_xboole_0(k3_xboole_0('#skF_4', A_53), A_3) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_53)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_4])).
% 3.97/1.68  tff(c_325, plain, (![A_73, A_74]: (k3_xboole_0(k3_xboole_0('#skF_4', A_73), A_74)=A_74 | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_73)) | ~r1_tarski(A_74, k3_xboole_0('#skF_4', A_73)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_73)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_183])).
% 3.97/1.68  tff(c_328, plain, (![B_8, A_74]: (k3_xboole_0(k3_xboole_0('#skF_4', B_8), A_74)=A_74 | ~r1_tarski(A_74, k3_xboole_0('#skF_4', B_8)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), B_8)) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_10, c_325])).
% 3.97/1.68  tff(c_331, plain, (![B_8, A_74]: (k3_xboole_0(k3_xboole_0('#skF_4', B_8), A_74)=A_74 | ~r1_tarski(A_74, k3_xboole_0('#skF_4', B_8)) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), B_8)) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_328])).
% 3.97/1.68  tff(c_339, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_331])).
% 3.97/1.68  tff(c_342, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_339])).
% 3.97/1.68  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_342])).
% 3.97/1.68  tff(c_348, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_331])).
% 3.97/1.68  tff(c_293, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_1'(A_68, B_69, C_70), k1_relat_1(B_69)) | k7_relat_1(C_70, A_68)=B_69 | k3_xboole_0(k1_relat_1(C_70), A_68)!=k1_relat_1(B_69) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.68  tff(c_317, plain, (![A_68, C_70]: (r2_hidden('#skF_1'(A_68, k7_relat_1('#skF_3', '#skF_4'), C_70), '#skF_4') | k7_relat_1(C_70, A_68)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_70), A_68)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_71, c_293])).
% 3.97/1.68  tff(c_323, plain, (![A_68, C_70]: (r2_hidden('#skF_1'(A_68, k7_relat_1('#skF_3', '#skF_4'), C_70), '#skF_4') | k7_relat_1(C_70, A_68)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_70), A_68)!='#skF_4' | ~v1_funct_1(C_70) | ~v1_relat_1(C_70) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_71, c_317])).
% 3.97/1.68  tff(c_581, plain, (![A_68, C_70]: (r2_hidden('#skF_1'(A_68, k7_relat_1('#skF_3', '#skF_4'), C_70), '#skF_4') | k7_relat_1(C_70, A_68)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_70), A_68)!='#skF_4' | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_323])).
% 3.97/1.68  tff(c_582, plain, (![A_102, C_103]: (r2_hidden('#skF_1'(A_102, k7_relat_1('#skF_3', '#skF_4'), C_103), '#skF_4') | k7_relat_1(C_103, A_102)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_103), A_102)!='#skF_4' | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_323])).
% 3.97/1.68  tff(c_36, plain, (![D_37]: (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5') | k1_funct_1('#skF_2', D_37)=k1_funct_1('#skF_3', D_37) | ~r2_hidden(D_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_137, plain, (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 3.97/1.68  tff(c_38, plain, (![D_37]: (r2_hidden('#skF_5', '#skF_4') | k1_funct_1('#skF_2', D_37)=k1_funct_1('#skF_3', D_37) | ~r2_hidden(D_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_95, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 3.97/1.68  tff(c_40, plain, (![D_37]: (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4') | k1_funct_1('#skF_2', D_37)=k1_funct_1('#skF_3', D_37) | ~r2_hidden(D_37, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_154, plain, (![D_51]: (k1_funct_1('#skF_2', D_51)=k1_funct_1('#skF_3', D_51) | ~r2_hidden(D_51, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_40])).
% 3.97/1.68  tff(c_157, plain, (k1_funct_1('#skF_2', '#skF_5')=k1_funct_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_95, c_154])).
% 3.97/1.68  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_157])).
% 3.97/1.68  tff(c_162, plain, (![D_37]: (k1_funct_1('#skF_2', D_37)=k1_funct_1('#skF_3', D_37) | ~r2_hidden(D_37, '#skF_4'))), inference(splitRight, [status(thm)], [c_36])).
% 3.97/1.68  tff(c_667, plain, (![A_114, C_115]: (k1_funct_1('#skF_2', '#skF_1'(A_114, k7_relat_1('#skF_3', '#skF_4'), C_115))=k1_funct_1('#skF_3', '#skF_1'(A_114, k7_relat_1('#skF_3', '#skF_4'), C_115)) | k7_relat_1(C_115, A_114)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_115), A_114)!='#skF_4' | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_582, c_162])).
% 3.97/1.68  tff(c_16, plain, (![C_18, B_17, A_16]: (k1_funct_1(k7_relat_1(C_18, B_17), A_16)=k1_funct_1(C_18, A_16) | ~r2_hidden(A_16, B_17) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.68  tff(c_353, plain, (![C_79, A_80, B_81]: (k1_funct_1(C_79, '#skF_1'(A_80, B_81, C_79))!=k1_funct_1(B_81, '#skF_1'(A_80, B_81, C_79)) | k7_relat_1(C_79, A_80)=B_81 | k3_xboole_0(k1_relat_1(C_79), A_80)!=k1_relat_1(B_81) | ~v1_funct_1(C_79) | ~v1_relat_1(C_79) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.68  tff(c_359, plain, (![C_79, A_80, C_18, B_17]: (k1_funct_1(C_79, '#skF_1'(A_80, k7_relat_1(C_18, B_17), C_79))!=k1_funct_1(C_18, '#skF_1'(A_80, k7_relat_1(C_18, B_17), C_79)) | k7_relat_1(C_79, A_80)=k7_relat_1(C_18, B_17) | k3_xboole_0(k1_relat_1(C_79), A_80)!=k1_relat_1(k7_relat_1(C_18, B_17)) | ~v1_funct_1(C_79) | ~v1_relat_1(C_79) | ~v1_funct_1(k7_relat_1(C_18, B_17)) | ~v1_relat_1(k7_relat_1(C_18, B_17)) | ~r2_hidden('#skF_1'(A_80, k7_relat_1(C_18, B_17), C_79), B_17) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_353])).
% 3.97/1.68  tff(c_673, plain, (![A_114]: (k3_xboole_0(k1_relat_1('#skF_2'), A_114)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_114, k7_relat_1('#skF_3', '#skF_4'), '#skF_2'), '#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k7_relat_1('#skF_2', A_114)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_114)!='#skF_4' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_667, c_359])).
% 3.97/1.68  tff(c_682, plain, (![A_116]: (~r2_hidden('#skF_1'(A_116, k7_relat_1('#skF_3', '#skF_4'), '#skF_2'), '#skF_4') | k7_relat_1('#skF_2', A_116)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_116)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_136, c_348, c_71, c_673])).
% 3.97/1.68  tff(c_686, plain, (![A_68]: (k7_relat_1('#skF_2', A_68)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_68)!='#skF_4' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_581, c_682])).
% 3.97/1.68  tff(c_705, plain, (![A_119]: (k7_relat_1('#skF_2', A_119)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_119)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_686])).
% 3.97/1.68  tff(c_709, plain, (![A_3]: (k7_relat_1('#skF_2', A_3)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_3))!='#skF_4' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_705])).
% 3.97/1.68  tff(c_712, plain, (![A_120]: (k7_relat_1('#skF_2', A_120)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_120))!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_709])).
% 3.97/1.68  tff(c_715, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_712])).
% 3.97/1.68  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_715])).
% 3.97/1.68  tff(c_720, plain, (![D_37]: (k1_funct_1('#skF_2', D_37)=k1_funct_1('#skF_3', D_37) | ~r2_hidden(D_37, '#skF_4'))), inference(splitRight, [status(thm)], [c_38])).
% 3.97/1.68  tff(c_1252, plain, (![A_184, C_185]: (k1_funct_1('#skF_2', '#skF_1'(A_184, k7_relat_1('#skF_3', '#skF_4'), C_185))=k1_funct_1('#skF_3', '#skF_1'(A_184, k7_relat_1('#skF_3', '#skF_4'), C_185)) | k7_relat_1(C_185, A_184)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_185), A_184)!='#skF_4' | ~v1_funct_1(C_185) | ~v1_relat_1(C_185))), inference(resolution, [status(thm)], [c_1167, c_720])).
% 3.97/1.68  tff(c_938, plain, (![C_149, A_150, B_151]: (k1_funct_1(C_149, '#skF_1'(A_150, B_151, C_149))!=k1_funct_1(B_151, '#skF_1'(A_150, B_151, C_149)) | k7_relat_1(C_149, A_150)=B_151 | k3_xboole_0(k1_relat_1(C_149), A_150)!=k1_relat_1(B_151) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149) | ~v1_funct_1(B_151) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.68  tff(c_944, plain, (![C_18, A_150, B_17, C_149]: (k1_funct_1(C_18, '#skF_1'(A_150, k7_relat_1(C_18, B_17), C_149))!=k1_funct_1(C_149, '#skF_1'(A_150, k7_relat_1(C_18, B_17), C_149)) | k7_relat_1(C_18, B_17)=k7_relat_1(C_149, A_150) | k3_xboole_0(k1_relat_1(C_149), A_150)!=k1_relat_1(k7_relat_1(C_18, B_17)) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149) | ~v1_funct_1(k7_relat_1(C_18, B_17)) | ~v1_relat_1(k7_relat_1(C_18, B_17)) | ~r2_hidden('#skF_1'(A_150, k7_relat_1(C_18, B_17), C_149), B_17) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_938])).
% 3.97/1.68  tff(c_1258, plain, (![A_184]: (k3_xboole_0(k1_relat_1('#skF_2'), A_184)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_184, k7_relat_1('#skF_3', '#skF_4'), '#skF_2'), '#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k7_relat_1('#skF_2', A_184)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_184)!='#skF_4' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1252, c_944])).
% 3.97/1.68  tff(c_1267, plain, (![A_186]: (~r2_hidden('#skF_1'(A_186, k7_relat_1('#skF_3', '#skF_4'), '#skF_2'), '#skF_4') | k7_relat_1('#skF_2', A_186)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_186)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_733, c_877, c_71, c_1258])).
% 3.97/1.68  tff(c_1271, plain, (![A_138]: (k7_relat_1('#skF_2', A_138)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_138)!='#skF_4' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_1166, c_1267])).
% 3.97/1.68  tff(c_1290, plain, (![A_189]: (k7_relat_1('#skF_2', A_189)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_189)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1271])).
% 3.97/1.68  tff(c_1294, plain, (![A_3]: (k7_relat_1('#skF_2', A_3)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_3))!='#skF_4' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1290])).
% 3.97/1.68  tff(c_1297, plain, (![A_190]: (k7_relat_1('#skF_2', A_190)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_190))!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1294])).
% 3.97/1.68  tff(c_1300, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_1297])).
% 3.97/1.68  tff(c_1304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1300])).
% 3.97/1.68  tff(c_1306, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 3.97/1.68  tff(c_30, plain, (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5') | k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.68  tff(c_1377, plain, (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_30])).
% 3.97/1.68  tff(c_1305, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 3.97/1.68  tff(c_1379, plain, (![C_197, B_198, A_199]: (k1_funct_1(k7_relat_1(C_197, B_198), A_199)=k1_funct_1(C_197, A_199) | ~r2_hidden(A_199, B_198) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.68  tff(c_1388, plain, (![A_199]: (k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_199)=k1_funct_1('#skF_2', A_199) | ~r2_hidden(A_199, '#skF_4') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_1379])).
% 3.97/1.68  tff(c_1393, plain, (![A_200]: (k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_200)=k1_funct_1('#skF_2', A_200) | ~r2_hidden(A_200, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1388])).
% 3.97/1.68  tff(c_1399, plain, (![A_200]: (k1_funct_1('#skF_2', A_200)=k1_funct_1('#skF_3', A_200) | ~r2_hidden(A_200, '#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r2_hidden(A_200, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1393, c_16])).
% 3.97/1.68  tff(c_1413, plain, (![A_201]: (k1_funct_1('#skF_2', A_201)=k1_funct_1('#skF_3', A_201) | ~r2_hidden(A_201, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_1399])).
% 3.97/1.68  tff(c_1416, plain, (k1_funct_1('#skF_2', '#skF_5')=k1_funct_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_1305, c_1413])).
% 3.97/1.68  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1377, c_1416])).
% 3.97/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.68  
% 3.97/1.68  Inference rules
% 3.97/1.68  ----------------------
% 3.97/1.68  #Ref     : 8
% 3.97/1.68  #Sup     : 299
% 3.97/1.68  #Fact    : 0
% 3.97/1.68  #Define  : 0
% 3.97/1.68  #Split   : 15
% 3.97/1.68  #Chain   : 0
% 3.97/1.68  #Close   : 0
% 3.97/1.68  
% 3.97/1.68  Ordering : KBO
% 3.97/1.68  
% 3.97/1.68  Simplification rules
% 3.97/1.68  ----------------------
% 3.97/1.68  #Subsume      : 32
% 3.97/1.68  #Demod        : 287
% 3.97/1.68  #Tautology    : 101
% 3.97/1.68  #SimpNegUnit  : 9
% 3.97/1.68  #BackRed      : 0
% 3.97/1.68  
% 3.97/1.68  #Partial instantiations: 0
% 3.97/1.68  #Strategies tried      : 1
% 3.97/1.68  
% 3.97/1.68  Timing (in seconds)
% 3.97/1.68  ----------------------
% 4.14/1.68  Preprocessing        : 0.31
% 4.14/1.68  Parsing              : 0.17
% 4.14/1.68  CNF conversion       : 0.02
% 4.14/1.68  Main loop            : 0.59
% 4.14/1.68  Inferencing          : 0.22
% 4.14/1.68  Reduction            : 0.18
% 4.14/1.68  Demodulation         : 0.12
% 4.14/1.68  BG Simplification    : 0.04
% 4.14/1.68  Subsumption          : 0.11
% 4.14/1.68  Abstraction          : 0.04
% 4.14/1.68  MUC search           : 0.00
% 4.14/1.68  Cooper               : 0.00
% 4.14/1.68  Total                : 0.95
% 4.14/1.68  Index Insertion      : 0.00
% 4.14/1.68  Index Deletion       : 0.00
% 4.14/1.68  Index Matching       : 0.00
% 4.14/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
