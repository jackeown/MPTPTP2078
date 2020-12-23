%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:29 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 552 expanded)
%              Number of leaves         :   22 ( 194 expanded)
%              Depth                    :   16
%              Number of atoms          :  318 (1964 expanded)
%              Number of equality atoms :  118 ( 582 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_91,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_30,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_41,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1156,plain,(
    ! [B_134,A_135] :
      ( k1_relat_1(k7_relat_1(B_134,A_135)) = A_135
      | ~ r1_tarski(A_135,k1_relat_1(B_134))
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1162,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1156])).

tff(c_1168,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1162])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(k1_relat_1(B_2),A_1) = k1_relat_1(k7_relat_1(B_2,A_1))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1159,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1156])).

tff(c_1165,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1159])).

tff(c_1175,plain,(
    ! [A_1] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_1)) = k3_xboole_0('#skF_4',A_1)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_2])).

tff(c_1189,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1175])).

tff(c_1193,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1189])).

tff(c_1197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_1193])).

tff(c_1199,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_funct_1(k7_relat_1(A_5,B_6))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [C_12,A_7,B_8] :
      ( k1_funct_1(C_12,'#skF_1'(A_7,B_8,C_12)) != k1_funct_1(B_8,'#skF_1'(A_7,B_8,C_12))
      | k7_relat_1(C_12,A_7) = B_8
      | k3_xboole_0(k1_relat_1(C_12),A_7) != k1_relat_1(B_8)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1461,plain,(
    ! [B_160,A_161] :
      ( k7_relat_1(B_160,A_161) = B_160
      | k3_xboole_0(k1_relat_1(B_160),A_161) != k1_relat_1(B_160)
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160)
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10])).

tff(c_1485,plain,(
    ! [A_161] :
      ( k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_161) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0('#skF_4',A_161) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_1461])).

tff(c_1494,plain,(
    ! [A_161] :
      ( k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_161) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0('#skF_4',A_161) != '#skF_4'
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1199,c_1165,c_1485])).

tff(c_1535,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1494])).

tff(c_1545,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1535])).

tff(c_1549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_1545])).

tff(c_1551,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1494])).

tff(c_1321,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_1'(A_148,B_149,C_150),k1_relat_1(B_149))
      | k7_relat_1(C_150,A_148) = B_149
      | k3_xboole_0(k1_relat_1(C_150),A_148) != k1_relat_1(B_149)
      | ~ v1_funct_1(C_150)
      | ~ v1_relat_1(C_150)
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1343,plain,(
    ! [A_148,C_150] :
      ( r2_hidden('#skF_1'(A_148,k7_relat_1('#skF_3','#skF_4'),C_150),'#skF_4')
      | k7_relat_1(C_150,A_148) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_150),A_148) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_150)
      | ~ v1_relat_1(C_150)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_1321])).

tff(c_1350,plain,(
    ! [A_148,C_150] :
      ( r2_hidden('#skF_1'(A_148,k7_relat_1('#skF_3','#skF_4'),C_150),'#skF_4')
      | k7_relat_1(C_150,A_148) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_150),A_148) != '#skF_4'
      | ~ v1_funct_1(C_150)
      | ~ v1_relat_1(C_150)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1165,c_1343])).

tff(c_1720,plain,(
    ! [A_176,C_177] :
      ( r2_hidden('#skF_1'(A_176,k7_relat_1('#skF_3','#skF_4'),C_177),'#skF_4')
      | k7_relat_1(C_177,A_176) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_177),A_176) != '#skF_4'
      | ~ v1_funct_1(C_177)
      | ~ v1_relat_1(C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_1350])).

tff(c_52,plain,(
    ! [B_42,A_43] :
      ( k1_relat_1(k7_relat_1(B_42,A_43)) = A_43
      | ~ r1_tarski(A_43,k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_64,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_58])).

tff(c_55,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_61,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_55])).

tff(c_71,plain,(
    ! [A_1] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_1)) = k3_xboole_0('#skF_4',A_1)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_85,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_88,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_88])).

tff(c_94,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_93,plain,(
    ! [A_1] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_1)) = k3_xboole_0('#skF_4',A_1) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_183,plain,(
    ! [C_49,B_50,A_51] :
      ( k1_funct_1(k7_relat_1(C_49,B_50),A_51) = k1_funct_1(C_49,A_51)
      | ~ r2_hidden(A_51,k1_relat_1(k7_relat_1(C_49,B_50)))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_189,plain,(
    ! [A_1,A_51] :
      ( k1_funct_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_1),A_51) = k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_51)
      | ~ r2_hidden(A_51,k3_xboole_0('#skF_4',A_1))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_183])).

tff(c_199,plain,(
    ! [A_1,A_51] :
      ( k1_funct_1(k7_relat_1(k7_relat_1('#skF_3','#skF_4'),A_1),A_51) = k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_51)
      | ~ r2_hidden(A_51,k3_xboole_0('#skF_4',A_1))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_189])).

tff(c_366,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_369,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_366])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_369])).

tff(c_375,plain,(
    v1_funct_1(k7_relat_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_387,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_1'(A_74,B_75,C_76),k1_relat_1(B_75))
      | k7_relat_1(C_76,A_74) = B_75
      | k3_xboole_0(k1_relat_1(C_76),A_74) != k1_relat_1(B_75)
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_415,plain,(
    ! [A_74,C_76] :
      ( r2_hidden('#skF_1'(A_74,k7_relat_1('#skF_3','#skF_4'),C_76),'#skF_4')
      | k7_relat_1(C_76,A_74) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_76),A_74) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76)
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_387])).

tff(c_428,plain,(
    ! [A_79,C_80] :
      ( r2_hidden('#skF_1'(A_79,k7_relat_1('#skF_3','#skF_4'),C_80),'#skF_4')
      | k7_relat_1(C_80,A_79) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_80),A_79) != '#skF_4'
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_375,c_61,c_415])).

tff(c_34,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5')
      | k1_funct_1('#skF_2',D_35) = k1_funct_1('#skF_3',D_35)
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_5','#skF_4')
      | k1_funct_1('#skF_2',D_35) = k1_funct_1('#skF_3',D_35)
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    ! [D_35] :
      ( k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4')
      | k1_funct_1('#skF_2',D_35) = k1_funct_1('#skF_3',D_35)
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_122,plain,(
    ! [D_45] :
      ( k1_funct_1('#skF_2',D_45) = k1_funct_1('#skF_3',D_45)
      | ~ r2_hidden(D_45,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_38])).

tff(c_125,plain,(
    k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_125])).

tff(c_130,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_2',D_35) = k1_funct_1('#skF_3',D_35)
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_432,plain,(
    ! [A_79,C_80] :
      ( k1_funct_1('#skF_2','#skF_1'(A_79,k7_relat_1('#skF_3','#skF_4'),C_80)) = k1_funct_1('#skF_3','#skF_1'(A_79,k7_relat_1('#skF_3','#skF_4'),C_80))
      | k7_relat_1(C_80,A_79) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_80),A_79) != '#skF_4'
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_428,c_130])).

tff(c_14,plain,(
    ! [C_16,B_15,A_14] :
      ( k1_funct_1(k7_relat_1(C_16,B_15),A_14) = k1_funct_1(C_16,A_14)
      | ~ r2_hidden(A_14,k1_relat_1(k7_relat_1(C_16,B_15)))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_596,plain,(
    ! [C_90,B_91,A_92,C_93] :
      ( k1_funct_1(k7_relat_1(C_90,B_91),'#skF_1'(A_92,k7_relat_1(C_90,B_91),C_93)) = k1_funct_1(C_90,'#skF_1'(A_92,k7_relat_1(C_90,B_91),C_93))
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90)
      | k7_relat_1(C_93,A_92) = k7_relat_1(C_90,B_91)
      | k3_xboole_0(k1_relat_1(C_93),A_92) != k1_relat_1(k7_relat_1(C_90,B_91))
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93)
      | ~ v1_funct_1(k7_relat_1(C_90,B_91))
      | ~ v1_relat_1(k7_relat_1(C_90,B_91)) ) ),
    inference(resolution,[status(thm)],[c_387,c_14])).

tff(c_1030,plain,(
    ! [C_127,A_126,B_128,C_125] :
      ( k1_funct_1(C_127,'#skF_1'(A_126,k7_relat_1(C_127,B_128),C_125)) != k1_funct_1(C_125,'#skF_1'(A_126,k7_relat_1(C_127,B_128),C_125))
      | k7_relat_1(C_127,B_128) = k7_relat_1(C_125,A_126)
      | k3_xboole_0(k1_relat_1(C_125),A_126) != k1_relat_1(k7_relat_1(C_127,B_128))
      | ~ v1_funct_1(C_125)
      | ~ v1_relat_1(C_125)
      | ~ v1_funct_1(k7_relat_1(C_127,B_128))
      | ~ v1_relat_1(k7_relat_1(C_127,B_128))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127)
      | k7_relat_1(C_127,B_128) = k7_relat_1(C_125,A_126)
      | k3_xboole_0(k1_relat_1(C_125),A_126) != k1_relat_1(k7_relat_1(C_127,B_128))
      | ~ v1_funct_1(C_125)
      | ~ v1_relat_1(C_125)
      | ~ v1_funct_1(k7_relat_1(C_127,B_128))
      | ~ v1_relat_1(k7_relat_1(C_127,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_10])).

tff(c_1050,plain,(
    ! [A_79] :
      ( ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_79) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | k7_relat_1('#skF_2',A_79) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_79) != '#skF_4'
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_1030])).

tff(c_1128,plain,(
    ! [A_129] :
      ( k7_relat_1('#skF_2',A_129) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_129) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_94,c_375,c_61,c_22,c_20,c_1050])).

tff(c_1132,plain,(
    ! [A_1] :
      ( k7_relat_1('#skF_2',A_1) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_1)) != '#skF_4'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1128])).

tff(c_1135,plain,(
    ! [A_130] :
      ( k7_relat_1('#skF_2',A_130) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_130)) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1132])).

tff(c_1138,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1135])).

tff(c_1142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_1138])).

tff(c_1143,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_2',D_35) = k1_funct_1('#skF_3',D_35)
      | ~ r2_hidden(D_35,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1724,plain,(
    ! [A_176,C_177] :
      ( k1_funct_1('#skF_2','#skF_1'(A_176,k7_relat_1('#skF_3','#skF_4'),C_177)) = k1_funct_1('#skF_3','#skF_1'(A_176,k7_relat_1('#skF_3','#skF_4'),C_177))
      | k7_relat_1(C_177,A_176) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1(C_177),A_176) != '#skF_4'
      | ~ v1_funct_1(C_177)
      | ~ v1_relat_1(C_177) ) ),
    inference(resolution,[status(thm)],[c_1720,c_1143])).

tff(c_1608,plain,(
    ! [C_170,B_171,A_172,C_173] :
      ( k1_funct_1(k7_relat_1(C_170,B_171),'#skF_1'(A_172,k7_relat_1(C_170,B_171),C_173)) = k1_funct_1(C_170,'#skF_1'(A_172,k7_relat_1(C_170,B_171),C_173))
      | ~ v1_funct_1(C_170)
      | ~ v1_relat_1(C_170)
      | k7_relat_1(C_173,A_172) = k7_relat_1(C_170,B_171)
      | k3_xboole_0(k1_relat_1(C_173),A_172) != k1_relat_1(k7_relat_1(C_170,B_171))
      | ~ v1_funct_1(C_173)
      | ~ v1_relat_1(C_173)
      | ~ v1_funct_1(k7_relat_1(C_170,B_171))
      | ~ v1_relat_1(k7_relat_1(C_170,B_171)) ) ),
    inference(resolution,[status(thm)],[c_1321,c_14])).

tff(c_1887,plain,(
    ! [C_198,A_197,B_199,C_196] :
      ( k1_funct_1(C_198,'#skF_1'(A_197,k7_relat_1(C_198,B_199),C_196)) != k1_funct_1(C_196,'#skF_1'(A_197,k7_relat_1(C_198,B_199),C_196))
      | k7_relat_1(C_198,B_199) = k7_relat_1(C_196,A_197)
      | k3_xboole_0(k1_relat_1(C_196),A_197) != k1_relat_1(k7_relat_1(C_198,B_199))
      | ~ v1_funct_1(C_196)
      | ~ v1_relat_1(C_196)
      | ~ v1_funct_1(k7_relat_1(C_198,B_199))
      | ~ v1_relat_1(k7_relat_1(C_198,B_199))
      | ~ v1_funct_1(C_198)
      | ~ v1_relat_1(C_198)
      | k7_relat_1(C_198,B_199) = k7_relat_1(C_196,A_197)
      | k3_xboole_0(k1_relat_1(C_196),A_197) != k1_relat_1(k7_relat_1(C_198,B_199))
      | ~ v1_funct_1(C_196)
      | ~ v1_relat_1(C_196)
      | ~ v1_funct_1(k7_relat_1(C_198,B_199))
      | ~ v1_relat_1(k7_relat_1(C_198,B_199)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_10])).

tff(c_1899,plain,(
    ! [A_176] :
      ( ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_176) != k1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_funct_1(k7_relat_1('#skF_3','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_4'))
      | k7_relat_1('#skF_2',A_176) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_176) != '#skF_4'
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_1887])).

tff(c_1980,plain,(
    ! [A_200] :
      ( k7_relat_1('#skF_2',A_200) = k7_relat_1('#skF_3','#skF_4')
      | k3_xboole_0(k1_relat_1('#skF_2'),A_200) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1199,c_1551,c_1165,c_22,c_20,c_1899])).

tff(c_1984,plain,(
    ! [A_1] :
      ( k7_relat_1('#skF_2',A_1) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_1)) != '#skF_4'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1980])).

tff(c_1987,plain,(
    ! [A_201] :
      ( k7_relat_1('#skF_2',A_201) = k7_relat_1('#skF_3','#skF_4')
      | k1_relat_1(k7_relat_1('#skF_2',A_201)) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1984])).

tff(c_1990,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_1987])).

tff(c_1994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_1990])).

tff(c_1996,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5')
    | k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2035,plain,(
    k1_funct_1('#skF_2','#skF_5') != k1_funct_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_28])).

tff(c_1995,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2021,plain,(
    ! [B_204,A_205] :
      ( k1_relat_1(k7_relat_1(B_204,A_205)) = A_205
      | ~ r1_tarski(A_205,k1_relat_1(B_204))
      | ~ v1_relat_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2024,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_2021])).

tff(c_2030,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2024])).

tff(c_2069,plain,(
    ! [C_208,B_209,A_210] :
      ( k1_funct_1(k7_relat_1(C_208,B_209),A_210) = k1_funct_1(C_208,A_210)
      | ~ r2_hidden(A_210,k1_relat_1(k7_relat_1(C_208,B_209)))
      | ~ v1_funct_1(C_208)
      | ~ v1_relat_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2075,plain,(
    ! [A_210] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_210) = k1_funct_1('#skF_3',A_210)
      | ~ r2_hidden(A_210,'#skF_4')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2030,c_2069])).

tff(c_2094,plain,(
    ! [A_212] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_212) = k1_funct_1('#skF_3',A_212)
      | ~ r2_hidden(A_212,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_2075])).

tff(c_2078,plain,(
    ! [A_210] :
      ( k1_funct_1(k7_relat_1('#skF_2','#skF_4'),A_210) = k1_funct_1('#skF_2',A_210)
      | ~ r2_hidden(A_210,k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1996,c_2069])).

tff(c_2084,plain,(
    ! [A_210] :
      ( k1_funct_1(k7_relat_1('#skF_3','#skF_4'),A_210) = k1_funct_1('#skF_2',A_210)
      | ~ r2_hidden(A_210,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_2030,c_1996,c_2078])).

tff(c_2124,plain,(
    ! [A_216] :
      ( k1_funct_1('#skF_2',A_216) = k1_funct_1('#skF_3',A_216)
      | ~ r2_hidden(A_216,'#skF_4')
      | ~ r2_hidden(A_216,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2094,c_2084])).

tff(c_2126,plain,
    ( k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1995,c_2124])).

tff(c_2129,plain,(
    k1_funct_1('#skF_2','#skF_5') = k1_funct_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_2126])).

tff(c_2131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2035,c_2129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.85  
% 4.80/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.85  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.80/1.85  
% 4.80/1.85  %Foreground sorts:
% 4.80/1.85  
% 4.80/1.85  
% 4.80/1.85  %Background operators:
% 4.80/1.85  
% 4.80/1.85  
% 4.80/1.85  %Foreground operators:
% 4.80/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.80/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.80/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.80/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.80/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.80/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.85  
% 4.80/1.88  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 4.80/1.88  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.80/1.88  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 4.80/1.88  tff(f_43, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.80/1.88  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = k3_xboole_0(k1_relat_1(C), A)) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))) => (B = k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 4.80/1.88  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 4.80/1.88  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4') | k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_41, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 4.80/1.88  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_18, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_1156, plain, (![B_134, A_135]: (k1_relat_1(k7_relat_1(B_134, A_135))=A_135 | ~r1_tarski(A_135, k1_relat_1(B_134)) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.88  tff(c_1162, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_1156])).
% 4.80/1.88  tff(c_1168, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1162])).
% 4.80/1.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(k1_relat_1(B_2), A_1)=k1_relat_1(k7_relat_1(B_2, A_1)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.80/1.88  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.80/1.88  tff(c_16, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_1159, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1156])).
% 4.80/1.88  tff(c_1165, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1159])).
% 4.80/1.88  tff(c_1175, plain, (![A_1]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_1))=k3_xboole_0('#skF_4', A_1) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_2])).
% 4.80/1.88  tff(c_1189, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1175])).
% 4.80/1.88  tff(c_1193, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1189])).
% 4.80/1.88  tff(c_1197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_1193])).
% 4.80/1.88  tff(c_1199, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1175])).
% 4.80/1.88  tff(c_6, plain, (![A_5, B_6]: (v1_funct_1(k7_relat_1(A_5, B_6)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.80/1.88  tff(c_10, plain, (![C_12, A_7, B_8]: (k1_funct_1(C_12, '#skF_1'(A_7, B_8, C_12))!=k1_funct_1(B_8, '#skF_1'(A_7, B_8, C_12)) | k7_relat_1(C_12, A_7)=B_8 | k3_xboole_0(k1_relat_1(C_12), A_7)!=k1_relat_1(B_8) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.80/1.88  tff(c_1461, plain, (![B_160, A_161]: (k7_relat_1(B_160, A_161)=B_160 | k3_xboole_0(k1_relat_1(B_160), A_161)!=k1_relat_1(B_160) | ~v1_funct_1(B_160) | ~v1_relat_1(B_160) | ~v1_funct_1(B_160) | ~v1_relat_1(B_160))), inference(reflexivity, [status(thm), theory('equality')], [c_10])).
% 4.80/1.88  tff(c_1485, plain, (![A_161]: (k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_161)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0('#skF_4', A_161)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_1461])).
% 4.80/1.88  tff(c_1494, plain, (![A_161]: (k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_161)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0('#skF_4', A_161)!='#skF_4' | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1199, c_1165, c_1485])).
% 4.80/1.88  tff(c_1535, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1494])).
% 4.80/1.88  tff(c_1545, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1535])).
% 4.80/1.88  tff(c_1549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_1545])).
% 4.80/1.88  tff(c_1551, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1494])).
% 4.80/1.88  tff(c_1321, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_1'(A_148, B_149, C_150), k1_relat_1(B_149)) | k7_relat_1(C_150, A_148)=B_149 | k3_xboole_0(k1_relat_1(C_150), A_148)!=k1_relat_1(B_149) | ~v1_funct_1(C_150) | ~v1_relat_1(C_150) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.80/1.88  tff(c_1343, plain, (![A_148, C_150]: (r2_hidden('#skF_1'(A_148, k7_relat_1('#skF_3', '#skF_4'), C_150), '#skF_4') | k7_relat_1(C_150, A_148)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_150), A_148)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_150) | ~v1_relat_1(C_150) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_1321])).
% 4.80/1.88  tff(c_1350, plain, (![A_148, C_150]: (r2_hidden('#skF_1'(A_148, k7_relat_1('#skF_3', '#skF_4'), C_150), '#skF_4') | k7_relat_1(C_150, A_148)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_150), A_148)!='#skF_4' | ~v1_funct_1(C_150) | ~v1_relat_1(C_150) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1165, c_1343])).
% 4.80/1.88  tff(c_1720, plain, (![A_176, C_177]: (r2_hidden('#skF_1'(A_176, k7_relat_1('#skF_3', '#skF_4'), C_177), '#skF_4') | k7_relat_1(C_177, A_176)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_177), A_176)!='#skF_4' | ~v1_funct_1(C_177) | ~v1_relat_1(C_177))), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_1350])).
% 4.80/1.88  tff(c_52, plain, (![B_42, A_43]: (k1_relat_1(k7_relat_1(B_42, A_43))=A_43 | ~r1_tarski(A_43, k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.88  tff(c_58, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_52])).
% 4.80/1.88  tff(c_64, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_58])).
% 4.80/1.88  tff(c_55, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_52])).
% 4.80/1.88  tff(c_61, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_55])).
% 4.80/1.88  tff(c_71, plain, (![A_1]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_1))=k3_xboole_0('#skF_4', A_1) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 4.80/1.88  tff(c_85, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_71])).
% 4.80/1.88  tff(c_88, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_85])).
% 4.80/1.88  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_88])).
% 4.80/1.88  tff(c_94, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_71])).
% 4.80/1.88  tff(c_93, plain, (![A_1]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_1))=k3_xboole_0('#skF_4', A_1))), inference(splitRight, [status(thm)], [c_71])).
% 4.80/1.88  tff(c_183, plain, (![C_49, B_50, A_51]: (k1_funct_1(k7_relat_1(C_49, B_50), A_51)=k1_funct_1(C_49, A_51) | ~r2_hidden(A_51, k1_relat_1(k7_relat_1(C_49, B_50))) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/1.88  tff(c_189, plain, (![A_1, A_51]: (k1_funct_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_1), A_51)=k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_51) | ~r2_hidden(A_51, k3_xboole_0('#skF_4', A_1)) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_183])).
% 4.80/1.88  tff(c_199, plain, (![A_1, A_51]: (k1_funct_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_4'), A_1), A_51)=k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_51) | ~r2_hidden(A_51, k3_xboole_0('#skF_4', A_1)) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_189])).
% 4.80/1.88  tff(c_366, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_199])).
% 4.80/1.88  tff(c_369, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_366])).
% 4.80/1.88  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_369])).
% 4.80/1.88  tff(c_375, plain, (v1_funct_1(k7_relat_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_199])).
% 4.80/1.88  tff(c_387, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_1'(A_74, B_75, C_76), k1_relat_1(B_75)) | k7_relat_1(C_76, A_74)=B_75 | k3_xboole_0(k1_relat_1(C_76), A_74)!=k1_relat_1(B_75) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.80/1.88  tff(c_415, plain, (![A_74, C_76]: (r2_hidden('#skF_1'(A_74, k7_relat_1('#skF_3', '#skF_4'), C_76), '#skF_4') | k7_relat_1(C_76, A_74)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_76), A_74)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_387])).
% 4.80/1.88  tff(c_428, plain, (![A_79, C_80]: (r2_hidden('#skF_1'(A_79, k7_relat_1('#skF_3', '#skF_4'), C_80), '#skF_4') | k7_relat_1(C_80, A_79)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_80), A_79)!='#skF_4' | ~v1_funct_1(C_80) | ~v1_relat_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_375, c_61, c_415])).
% 4.80/1.88  tff(c_34, plain, (![D_35]: (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5') | k1_funct_1('#skF_2', D_35)=k1_funct_1('#skF_3', D_35) | ~r2_hidden(D_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_95, plain, (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 4.80/1.88  tff(c_36, plain, (![D_35]: (r2_hidden('#skF_5', '#skF_4') | k1_funct_1('#skF_2', D_35)=k1_funct_1('#skF_3', D_35) | ~r2_hidden(D_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_36])).
% 4.80/1.88  tff(c_38, plain, (![D_35]: (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4') | k1_funct_1('#skF_2', D_35)=k1_funct_1('#skF_3', D_35) | ~r2_hidden(D_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_122, plain, (![D_45]: (k1_funct_1('#skF_2', D_45)=k1_funct_1('#skF_3', D_45) | ~r2_hidden(D_45, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_41, c_38])).
% 4.80/1.88  tff(c_125, plain, (k1_funct_1('#skF_2', '#skF_5')=k1_funct_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_122])).
% 4.80/1.88  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_125])).
% 4.80/1.88  tff(c_130, plain, (![D_35]: (k1_funct_1('#skF_2', D_35)=k1_funct_1('#skF_3', D_35) | ~r2_hidden(D_35, '#skF_4'))), inference(splitRight, [status(thm)], [c_34])).
% 4.80/1.88  tff(c_432, plain, (![A_79, C_80]: (k1_funct_1('#skF_2', '#skF_1'(A_79, k7_relat_1('#skF_3', '#skF_4'), C_80))=k1_funct_1('#skF_3', '#skF_1'(A_79, k7_relat_1('#skF_3', '#skF_4'), C_80)) | k7_relat_1(C_80, A_79)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_80), A_79)!='#skF_4' | ~v1_funct_1(C_80) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_428, c_130])).
% 4.80/1.88  tff(c_14, plain, (![C_16, B_15, A_14]: (k1_funct_1(k7_relat_1(C_16, B_15), A_14)=k1_funct_1(C_16, A_14) | ~r2_hidden(A_14, k1_relat_1(k7_relat_1(C_16, B_15))) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/1.88  tff(c_596, plain, (![C_90, B_91, A_92, C_93]: (k1_funct_1(k7_relat_1(C_90, B_91), '#skF_1'(A_92, k7_relat_1(C_90, B_91), C_93))=k1_funct_1(C_90, '#skF_1'(A_92, k7_relat_1(C_90, B_91), C_93)) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90) | k7_relat_1(C_93, A_92)=k7_relat_1(C_90, B_91) | k3_xboole_0(k1_relat_1(C_93), A_92)!=k1_relat_1(k7_relat_1(C_90, B_91)) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93) | ~v1_funct_1(k7_relat_1(C_90, B_91)) | ~v1_relat_1(k7_relat_1(C_90, B_91)))), inference(resolution, [status(thm)], [c_387, c_14])).
% 4.80/1.88  tff(c_1030, plain, (![C_127, A_126, B_128, C_125]: (k1_funct_1(C_127, '#skF_1'(A_126, k7_relat_1(C_127, B_128), C_125))!=k1_funct_1(C_125, '#skF_1'(A_126, k7_relat_1(C_127, B_128), C_125)) | k7_relat_1(C_127, B_128)=k7_relat_1(C_125, A_126) | k3_xboole_0(k1_relat_1(C_125), A_126)!=k1_relat_1(k7_relat_1(C_127, B_128)) | ~v1_funct_1(C_125) | ~v1_relat_1(C_125) | ~v1_funct_1(k7_relat_1(C_127, B_128)) | ~v1_relat_1(k7_relat_1(C_127, B_128)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127) | k7_relat_1(C_127, B_128)=k7_relat_1(C_125, A_126) | k3_xboole_0(k1_relat_1(C_125), A_126)!=k1_relat_1(k7_relat_1(C_127, B_128)) | ~v1_funct_1(C_125) | ~v1_relat_1(C_125) | ~v1_funct_1(k7_relat_1(C_127, B_128)) | ~v1_relat_1(k7_relat_1(C_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_596, c_10])).
% 4.80/1.88  tff(c_1050, plain, (![A_79]: (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k3_xboole_0(k1_relat_1('#skF_2'), A_79)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | k7_relat_1('#skF_2', A_79)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_79)!='#skF_4' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_1030])).
% 4.80/1.88  tff(c_1128, plain, (![A_129]: (k7_relat_1('#skF_2', A_129)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_129)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_94, c_375, c_61, c_22, c_20, c_1050])).
% 4.80/1.88  tff(c_1132, plain, (![A_1]: (k7_relat_1('#skF_2', A_1)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_1))!='#skF_4' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1128])).
% 4.80/1.88  tff(c_1135, plain, (![A_130]: (k7_relat_1('#skF_2', A_130)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_130))!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1132])).
% 4.80/1.88  tff(c_1138, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_64, c_1135])).
% 4.80/1.88  tff(c_1142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_1138])).
% 4.80/1.88  tff(c_1143, plain, (![D_35]: (k1_funct_1('#skF_2', D_35)=k1_funct_1('#skF_3', D_35) | ~r2_hidden(D_35, '#skF_4'))), inference(splitRight, [status(thm)], [c_36])).
% 4.80/1.88  tff(c_1724, plain, (![A_176, C_177]: (k1_funct_1('#skF_2', '#skF_1'(A_176, k7_relat_1('#skF_3', '#skF_4'), C_177))=k1_funct_1('#skF_3', '#skF_1'(A_176, k7_relat_1('#skF_3', '#skF_4'), C_177)) | k7_relat_1(C_177, A_176)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1(C_177), A_176)!='#skF_4' | ~v1_funct_1(C_177) | ~v1_relat_1(C_177))), inference(resolution, [status(thm)], [c_1720, c_1143])).
% 4.80/1.88  tff(c_1608, plain, (![C_170, B_171, A_172, C_173]: (k1_funct_1(k7_relat_1(C_170, B_171), '#skF_1'(A_172, k7_relat_1(C_170, B_171), C_173))=k1_funct_1(C_170, '#skF_1'(A_172, k7_relat_1(C_170, B_171), C_173)) | ~v1_funct_1(C_170) | ~v1_relat_1(C_170) | k7_relat_1(C_173, A_172)=k7_relat_1(C_170, B_171) | k3_xboole_0(k1_relat_1(C_173), A_172)!=k1_relat_1(k7_relat_1(C_170, B_171)) | ~v1_funct_1(C_173) | ~v1_relat_1(C_173) | ~v1_funct_1(k7_relat_1(C_170, B_171)) | ~v1_relat_1(k7_relat_1(C_170, B_171)))), inference(resolution, [status(thm)], [c_1321, c_14])).
% 4.80/1.88  tff(c_1887, plain, (![C_198, A_197, B_199, C_196]: (k1_funct_1(C_198, '#skF_1'(A_197, k7_relat_1(C_198, B_199), C_196))!=k1_funct_1(C_196, '#skF_1'(A_197, k7_relat_1(C_198, B_199), C_196)) | k7_relat_1(C_198, B_199)=k7_relat_1(C_196, A_197) | k3_xboole_0(k1_relat_1(C_196), A_197)!=k1_relat_1(k7_relat_1(C_198, B_199)) | ~v1_funct_1(C_196) | ~v1_relat_1(C_196) | ~v1_funct_1(k7_relat_1(C_198, B_199)) | ~v1_relat_1(k7_relat_1(C_198, B_199)) | ~v1_funct_1(C_198) | ~v1_relat_1(C_198) | k7_relat_1(C_198, B_199)=k7_relat_1(C_196, A_197) | k3_xboole_0(k1_relat_1(C_196), A_197)!=k1_relat_1(k7_relat_1(C_198, B_199)) | ~v1_funct_1(C_196) | ~v1_relat_1(C_196) | ~v1_funct_1(k7_relat_1(C_198, B_199)) | ~v1_relat_1(k7_relat_1(C_198, B_199)))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_10])).
% 4.80/1.88  tff(c_1899, plain, (![A_176]: (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k3_xboole_0(k1_relat_1('#skF_2'), A_176)!=k1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_4')) | k7_relat_1('#skF_2', A_176)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_176)!='#skF_4' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1724, c_1887])).
% 4.80/1.88  tff(c_1980, plain, (![A_200]: (k7_relat_1('#skF_2', A_200)=k7_relat_1('#skF_3', '#skF_4') | k3_xboole_0(k1_relat_1('#skF_2'), A_200)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1199, c_1551, c_1165, c_22, c_20, c_1899])).
% 4.80/1.88  tff(c_1984, plain, (![A_1]: (k7_relat_1('#skF_2', A_1)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_1))!='#skF_4' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1980])).
% 4.80/1.88  tff(c_1987, plain, (![A_201]: (k7_relat_1('#skF_2', A_201)=k7_relat_1('#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_2', A_201))!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1984])).
% 4.80/1.88  tff(c_1990, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1168, c_1987])).
% 4.80/1.88  tff(c_1994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_1990])).
% 4.80/1.88  tff(c_1996, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 4.80/1.88  tff(c_28, plain, (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5') | k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.80/1.88  tff(c_2035, plain, (k1_funct_1('#skF_2', '#skF_5')!=k1_funct_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1996, c_28])).
% 4.80/1.88  tff(c_1995, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 4.80/1.88  tff(c_2021, plain, (![B_204, A_205]: (k1_relat_1(k7_relat_1(B_204, A_205))=A_205 | ~r1_tarski(A_205, k1_relat_1(B_204)) | ~v1_relat_1(B_204))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.88  tff(c_2024, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_2021])).
% 4.80/1.88  tff(c_2030, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2024])).
% 4.80/1.88  tff(c_2069, plain, (![C_208, B_209, A_210]: (k1_funct_1(k7_relat_1(C_208, B_209), A_210)=k1_funct_1(C_208, A_210) | ~r2_hidden(A_210, k1_relat_1(k7_relat_1(C_208, B_209))) | ~v1_funct_1(C_208) | ~v1_relat_1(C_208))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/1.88  tff(c_2075, plain, (![A_210]: (k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_210)=k1_funct_1('#skF_3', A_210) | ~r2_hidden(A_210, '#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2030, c_2069])).
% 4.80/1.88  tff(c_2094, plain, (![A_212]: (k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_212)=k1_funct_1('#skF_3', A_212) | ~r2_hidden(A_212, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_2075])).
% 4.80/1.88  tff(c_2078, plain, (![A_210]: (k1_funct_1(k7_relat_1('#skF_2', '#skF_4'), A_210)=k1_funct_1('#skF_2', A_210) | ~r2_hidden(A_210, k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1996, c_2069])).
% 4.80/1.88  tff(c_2084, plain, (![A_210]: (k1_funct_1(k7_relat_1('#skF_3', '#skF_4'), A_210)=k1_funct_1('#skF_2', A_210) | ~r2_hidden(A_210, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_2030, c_1996, c_2078])).
% 4.80/1.88  tff(c_2124, plain, (![A_216]: (k1_funct_1('#skF_2', A_216)=k1_funct_1('#skF_3', A_216) | ~r2_hidden(A_216, '#skF_4') | ~r2_hidden(A_216, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2094, c_2084])).
% 4.80/1.88  tff(c_2126, plain, (k1_funct_1('#skF_2', '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1995, c_2124])).
% 4.80/1.88  tff(c_2129, plain, (k1_funct_1('#skF_2', '#skF_5')=k1_funct_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_2126])).
% 4.80/1.88  tff(c_2131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2035, c_2129])).
% 4.80/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.88  
% 4.80/1.88  Inference rules
% 4.80/1.88  ----------------------
% 4.80/1.88  #Ref     : 4
% 4.80/1.88  #Sup     : 454
% 4.80/1.88  #Fact    : 0
% 4.80/1.88  #Define  : 0
% 4.80/1.88  #Split   : 18
% 4.80/1.88  #Chain   : 0
% 4.80/1.88  #Close   : 0
% 4.80/1.88  
% 4.80/1.88  Ordering : KBO
% 4.80/1.88  
% 4.80/1.88  Simplification rules
% 4.80/1.88  ----------------------
% 4.80/1.88  #Subsume      : 29
% 4.80/1.88  #Demod        : 493
% 4.80/1.88  #Tautology    : 169
% 4.80/1.88  #SimpNegUnit  : 8
% 4.80/1.88  #BackRed      : 0
% 4.80/1.88  
% 4.80/1.88  #Partial instantiations: 0
% 4.80/1.88  #Strategies tried      : 1
% 4.80/1.88  
% 4.80/1.88  Timing (in seconds)
% 4.80/1.88  ----------------------
% 4.80/1.88  Preprocessing        : 0.32
% 4.80/1.88  Parsing              : 0.17
% 4.80/1.88  CNF conversion       : 0.02
% 4.80/1.88  Main loop            : 0.76
% 4.80/1.88  Inferencing          : 0.28
% 4.80/1.88  Reduction            : 0.25
% 4.80/1.88  Demodulation         : 0.18
% 4.80/1.88  BG Simplification    : 0.05
% 4.80/1.88  Subsumption          : 0.14
% 4.80/1.88  Abstraction          : 0.06
% 4.80/1.88  MUC search           : 0.00
% 4.80/1.88  Cooper               : 0.00
% 4.80/1.88  Total                : 1.13
% 4.80/1.88  Index Insertion      : 0.00
% 4.80/1.88  Index Deletion       : 0.00
% 4.80/1.88  Index Matching       : 0.00
% 4.80/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
