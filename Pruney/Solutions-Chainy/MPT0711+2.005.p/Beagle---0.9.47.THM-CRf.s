%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:30 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 462 expanded)
%              Number of leaves         :   29 ( 175 expanded)
%              Depth                    :   17
%              Number of atoms          :  179 (1282 expanded)
%              Number of equality atoms :   61 ( 503 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( k1_relat_1(A) = k1_relat_1(B)
                  & ! [D] :
                      ( r2_hidden(D,C)
                     => k1_funct_1(A,D) = k1_funct_1(B,D) ) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_68,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_89,axiom,(
    ! [A] :
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

tff(c_38,plain,(
    k7_relat_1('#skF_5','#skF_6') != k7_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_152,plain,(
    ! [B_80,A_81] :
      ( k3_xboole_0(k1_relat_1(B_80),A_81) = k1_relat_1(k7_relat_1(B_80,A_81))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_161,plain,(
    ! [A_81] :
      ( k3_xboole_0(k1_relat_1('#skF_4'),A_81) = k1_relat_1(k7_relat_1('#skF_5',A_81))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_152])).

tff(c_171,plain,(
    ! [A_82] : k3_xboole_0(k1_relat_1('#skF_4'),A_82) = k1_relat_1(k7_relat_1('#skF_5',A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_161])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_177,plain,(
    ! [A_82] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_82)) = k1_relat_1(k7_relat_1('#skF_4',A_82))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_20])).

tff(c_187,plain,(
    ! [A_82] : k1_relat_1(k7_relat_1('#skF_5',A_82)) = k1_relat_1(k7_relat_1('#skF_4',A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_177])).

tff(c_168,plain,(
    ! [A_81] : k3_xboole_0(k1_relat_1('#skF_4'),A_81) = k1_relat_1(k7_relat_1('#skF_5',A_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_161])).

tff(c_268,plain,(
    ! [A_81] : k3_xboole_0(k1_relat_1('#skF_4'),A_81) = k1_relat_1(k7_relat_1('#skF_4',A_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_168])).

tff(c_30,plain,(
    ! [A_19] : v1_relat_1('#skF_2'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_19] : k1_relat_1('#skF_2'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_164,plain,(
    ! [A_19,A_81] :
      ( k1_relat_1(k7_relat_1('#skF_2'(A_19),A_81)) = k3_xboole_0(A_19,A_81)
      | ~ v1_relat_1('#skF_2'(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_152])).

tff(c_170,plain,(
    ! [A_19,A_81] : k1_relat_1(k7_relat_1('#skF_2'(A_19),A_81)) = k3_xboole_0(A_19,A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_164])).

tff(c_85,plain,(
    ! [A_67] :
      ( k7_relat_1(A_67,k1_relat_1(A_67)) = A_67
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [A_19] :
      ( k7_relat_1('#skF_2'(A_19),A_19) = '#skF_2'(A_19)
      | ~ v1_relat_1('#skF_2'(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_103,plain,(
    ! [A_19] : k7_relat_1('#skF_2'(A_19),A_19) = '#skF_2'(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_97])).

tff(c_455,plain,(
    ! [C_95,A_96,B_97] :
      ( k7_relat_1(k7_relat_1(C_95,A_96),B_97) = k7_relat_1(C_95,k3_xboole_0(A_96,B_97))
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_481,plain,(
    ! [A_19,B_97] :
      ( k7_relat_1('#skF_2'(A_19),k3_xboole_0(A_19,B_97)) = k7_relat_1('#skF_2'(A_19),B_97)
      | ~ v1_relat_1('#skF_2'(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_455])).

tff(c_620,plain,(
    ! [A_104,B_105] : k7_relat_1('#skF_2'(A_104),k3_xboole_0(A_104,B_105)) = k7_relat_1('#skF_2'(A_104),B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_481])).

tff(c_632,plain,(
    ! [A_104,B_105] : k3_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k1_relat_1(k7_relat_1('#skF_2'(A_104),B_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_170])).

tff(c_653,plain,(
    ! [A_106,B_107] : k3_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_632])).

tff(c_682,plain,(
    ! [A_81] : k3_xboole_0(k1_relat_1('#skF_4'),k1_relat_1(k7_relat_1('#skF_4',A_81))) = k3_xboole_0(k1_relat_1('#skF_4'),A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_653])).

tff(c_703,plain,(
    ! [A_81] : k3_xboole_0(k1_relat_1('#skF_4'),k1_relat_1(k7_relat_1('#skF_4',A_81))) = k1_relat_1(k7_relat_1('#skF_4',A_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_682])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_798,plain,(
    ! [A_112,C_113,B_114] :
      ( r2_hidden(A_112,k1_relat_1(C_113))
      | ~ r2_hidden(A_112,k1_relat_1(k7_relat_1(C_113,B_114)))
      | ~ v1_relat_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_830,plain,(
    ! [A_112,A_19,A_81] :
      ( r2_hidden(A_112,k1_relat_1('#skF_2'(A_19)))
      | ~ r2_hidden(A_112,k3_xboole_0(A_19,A_81))
      | ~ v1_relat_1('#skF_2'(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_798])).

tff(c_863,plain,(
    ! [A_115,A_116,A_117] :
      ( r2_hidden(A_115,A_116)
      | ~ r2_hidden(A_115,k3_xboole_0(A_116,A_117)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_830])).

tff(c_1288,plain,(
    ! [A_138,A_139,B_140] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_138,A_139),B_140),A_138)
      | r1_tarski(k3_xboole_0(A_138,A_139),B_140) ) ),
    inference(resolution,[status(thm)],[c_6,c_863])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1351,plain,(
    ! [A_141,A_142] : r1_tarski(k3_xboole_0(A_141,A_142),A_141) ),
    inference(resolution,[status(thm)],[c_1288,c_4])).

tff(c_1354,plain,(
    ! [A_81] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_81)),k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_1351])).

tff(c_22,plain,(
    ! [A_18] :
      ( k7_relat_1(A_18,k1_relat_1(A_18)) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1505,plain,(
    ! [A_149,B_150] :
      ( k7_relat_1(A_149,k3_xboole_0(k1_relat_1(A_149),B_150)) = k7_relat_1(A_149,B_150)
      | ~ v1_relat_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_455])).

tff(c_1593,plain,(
    ! [A_81] :
      ( k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4',A_81))) = k7_relat_1('#skF_4',A_81)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_1505])).

tff(c_1643,plain,(
    ! [A_81] : k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4',A_81))) = k7_relat_1('#skF_4',A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_1593])).

tff(c_94,plain,
    ( k7_relat_1('#skF_5',k1_relat_1('#skF_4')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_85])).

tff(c_101,plain,(
    k7_relat_1('#skF_5',k1_relat_1('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_94])).

tff(c_484,plain,(
    ! [B_97] :
      ( k7_relat_1('#skF_5',k3_xboole_0(k1_relat_1('#skF_4'),B_97)) = k7_relat_1('#skF_5',B_97)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_455])).

tff(c_497,plain,(
    ! [B_97] : k7_relat_1('#skF_5',k1_relat_1(k7_relat_1('#skF_4',B_97))) = k7_relat_1('#skF_5',B_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_268,c_484])).

tff(c_1366,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1351])).

tff(c_1388,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_3'(A_144,B_145,C_146),C_146)
      | k7_relat_1(B_145,C_146) = k7_relat_1(A_144,C_146)
      | ~ r1_tarski(C_146,k1_relat_1(B_145))
      | ~ r1_tarski(C_146,k1_relat_1(A_144))
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(A_13,B_14)
      | ~ r2_hidden(A_13,k1_relat_1(k7_relat_1(C_15,B_14)))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16057,plain,(
    ! [A_481,B_482,C_483,B_484] :
      ( r2_hidden('#skF_3'(A_481,B_482,k1_relat_1(k7_relat_1(C_483,B_484))),B_484)
      | ~ v1_relat_1(C_483)
      | k7_relat_1(B_482,k1_relat_1(k7_relat_1(C_483,B_484))) = k7_relat_1(A_481,k1_relat_1(k7_relat_1(C_483,B_484)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_483,B_484)),k1_relat_1(B_482))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_483,B_484)),k1_relat_1(A_481))
      | ~ v1_funct_1(B_482)
      | ~ v1_relat_1(B_482)
      | ~ v1_funct_1(A_481)
      | ~ v1_relat_1(A_481) ) ),
    inference(resolution,[status(thm)],[c_1388,c_18])).

tff(c_40,plain,(
    ! [D_58] :
      ( k1_funct_1('#skF_5',D_58) = k1_funct_1('#skF_4',D_58)
      | ~ r2_hidden(D_58,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16322,plain,(
    ! [A_485,B_486,C_487] :
      ( k1_funct_1('#skF_5','#skF_3'(A_485,B_486,k1_relat_1(k7_relat_1(C_487,'#skF_6')))) = k1_funct_1('#skF_4','#skF_3'(A_485,B_486,k1_relat_1(k7_relat_1(C_487,'#skF_6'))))
      | ~ v1_relat_1(C_487)
      | k7_relat_1(B_486,k1_relat_1(k7_relat_1(C_487,'#skF_6'))) = k7_relat_1(A_485,k1_relat_1(k7_relat_1(C_487,'#skF_6')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_487,'#skF_6')),k1_relat_1(B_486))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_487,'#skF_6')),k1_relat_1(A_485))
      | ~ v1_funct_1(B_486)
      | ~ v1_relat_1(B_486)
      | ~ v1_funct_1(A_485)
      | ~ v1_relat_1(A_485) ) ),
    inference(resolution,[status(thm)],[c_16057,c_40])).

tff(c_20855,plain,(
    ! [A_590,B_591] :
      ( k1_funct_1('#skF_5','#skF_3'(A_590,B_591,k1_relat_1(k7_relat_1(B_591,'#skF_6')))) = k1_funct_1('#skF_4','#skF_3'(A_590,B_591,k1_relat_1(k7_relat_1(B_591,'#skF_6'))))
      | k7_relat_1(B_591,k1_relat_1(k7_relat_1(B_591,'#skF_6'))) = k7_relat_1(A_590,k1_relat_1(k7_relat_1(B_591,'#skF_6')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_591,'#skF_6')),k1_relat_1(A_590))
      | ~ v1_funct_1(B_591)
      | ~ v1_funct_1(A_590)
      | ~ v1_relat_1(A_590)
      | ~ v1_relat_1(B_591) ) ),
    inference(resolution,[status(thm)],[c_1366,c_16322])).

tff(c_20906,plain,(
    ! [B_591] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_5',B_591,k1_relat_1(k7_relat_1(B_591,'#skF_6')))) = k1_funct_1('#skF_4','#skF_3'('#skF_5',B_591,k1_relat_1(k7_relat_1(B_591,'#skF_6'))))
      | k7_relat_1(B_591,k1_relat_1(k7_relat_1(B_591,'#skF_6'))) = k7_relat_1('#skF_5',k1_relat_1(k7_relat_1(B_591,'#skF_6')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_591,'#skF_6')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_591)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(B_591) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_20855])).

tff(c_22108,plain,(
    ! [B_603] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_5',B_603,k1_relat_1(k7_relat_1(B_603,'#skF_6')))) = k1_funct_1('#skF_4','#skF_3'('#skF_5',B_603,k1_relat_1(k7_relat_1(B_603,'#skF_6'))))
      | k7_relat_1(B_603,k1_relat_1(k7_relat_1(B_603,'#skF_6'))) = k7_relat_1('#skF_5',k1_relat_1(k7_relat_1(B_603,'#skF_6')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_603,'#skF_6')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_20906])).

tff(c_22126,plain,
    ( k1_funct_1('#skF_5','#skF_3'('#skF_5','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6')))) = k1_funct_1('#skF_4','#skF_3'('#skF_5','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6'))))
    | k7_relat_1('#skF_5',k1_relat_1(k7_relat_1('#skF_4','#skF_6'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1366,c_22108])).

tff(c_22152,plain,
    ( k1_funct_1('#skF_5','#skF_3'('#skF_5','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6')))) = k1_funct_1('#skF_4','#skF_3'('#skF_5','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6'))))
    | k7_relat_1('#skF_5','#skF_6') = k7_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1643,c_497,c_22126])).

tff(c_22153,plain,(
    k1_funct_1('#skF_5','#skF_3'('#skF_5','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6')))) = k1_funct_1('#skF_4','#skF_3'('#skF_5','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_22152])).

tff(c_34,plain,(
    ! [B_37,A_25,C_43] :
      ( k1_funct_1(B_37,'#skF_3'(A_25,B_37,C_43)) != k1_funct_1(A_25,'#skF_3'(A_25,B_37,C_43))
      | k7_relat_1(B_37,C_43) = k7_relat_1(A_25,C_43)
      | ~ r1_tarski(C_43,k1_relat_1(B_37))
      | ~ r1_tarski(C_43,k1_relat_1(A_25))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22570,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k7_relat_1('#skF_4','#skF_6'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_6')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_6')),k1_relat_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_6')),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22153,c_34])).

tff(c_22575,plain,(
    k7_relat_1('#skF_5','#skF_6') = k7_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_50,c_48,c_1354,c_42,c_1354,c_1643,c_497,c_22570])).

tff(c_22577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_22575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.88/4.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.92  
% 11.94/4.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.94/4.93  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 11.94/4.93  
% 11.94/4.93  %Foreground sorts:
% 11.94/4.93  
% 11.94/4.93  
% 11.94/4.93  %Background operators:
% 11.94/4.93  
% 11.94/4.93  
% 11.94/4.93  %Foreground operators:
% 11.94/4.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.94/4.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.94/4.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.94/4.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.94/4.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.94/4.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.94/4.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.94/4.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.94/4.93  tff('#skF_5', type, '#skF_5': $i).
% 11.94/4.93  tff('#skF_6', type, '#skF_6': $i).
% 11.94/4.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.94/4.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.94/4.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.94/4.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.94/4.93  tff('#skF_4', type, '#skF_4': $i).
% 11.94/4.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.94/4.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.94/4.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.94/4.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.94/4.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.94/4.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.94/4.93  
% 11.99/4.94  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 11.99/4.94  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 11.99/4.94  tff(f_68, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 11.99/4.94  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 11.99/4.94  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 11.99/4.94  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.99/4.94  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 11.99/4.94  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 11.99/4.94  tff(c_38, plain, (k7_relat_1('#skF_5', '#skF_6')!=k7_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_42, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_152, plain, (![B_80, A_81]: (k3_xboole_0(k1_relat_1(B_80), A_81)=k1_relat_1(k7_relat_1(B_80, A_81)) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.99/4.94  tff(c_161, plain, (![A_81]: (k3_xboole_0(k1_relat_1('#skF_4'), A_81)=k1_relat_1(k7_relat_1('#skF_5', A_81)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_152])).
% 11.99/4.94  tff(c_171, plain, (![A_82]: (k3_xboole_0(k1_relat_1('#skF_4'), A_82)=k1_relat_1(k7_relat_1('#skF_5', A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_161])).
% 11.99/4.94  tff(c_20, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.99/4.94  tff(c_177, plain, (![A_82]: (k1_relat_1(k7_relat_1('#skF_5', A_82))=k1_relat_1(k7_relat_1('#skF_4', A_82)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_20])).
% 11.99/4.94  tff(c_187, plain, (![A_82]: (k1_relat_1(k7_relat_1('#skF_5', A_82))=k1_relat_1(k7_relat_1('#skF_4', A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_177])).
% 11.99/4.94  tff(c_168, plain, (![A_81]: (k3_xboole_0(k1_relat_1('#skF_4'), A_81)=k1_relat_1(k7_relat_1('#skF_5', A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_161])).
% 11.99/4.94  tff(c_268, plain, (![A_81]: (k3_xboole_0(k1_relat_1('#skF_4'), A_81)=k1_relat_1(k7_relat_1('#skF_4', A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_168])).
% 11.99/4.94  tff(c_30, plain, (![A_19]: (v1_relat_1('#skF_2'(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.99/4.94  tff(c_26, plain, (![A_19]: (k1_relat_1('#skF_2'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.99/4.94  tff(c_164, plain, (![A_19, A_81]: (k1_relat_1(k7_relat_1('#skF_2'(A_19), A_81))=k3_xboole_0(A_19, A_81) | ~v1_relat_1('#skF_2'(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_152])).
% 11.99/4.94  tff(c_170, plain, (![A_19, A_81]: (k1_relat_1(k7_relat_1('#skF_2'(A_19), A_81))=k3_xboole_0(A_19, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_164])).
% 11.99/4.94  tff(c_85, plain, (![A_67]: (k7_relat_1(A_67, k1_relat_1(A_67))=A_67 | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.99/4.94  tff(c_97, plain, (![A_19]: (k7_relat_1('#skF_2'(A_19), A_19)='#skF_2'(A_19) | ~v1_relat_1('#skF_2'(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_85])).
% 11.99/4.94  tff(c_103, plain, (![A_19]: (k7_relat_1('#skF_2'(A_19), A_19)='#skF_2'(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_97])).
% 11.99/4.94  tff(c_455, plain, (![C_95, A_96, B_97]: (k7_relat_1(k7_relat_1(C_95, A_96), B_97)=k7_relat_1(C_95, k3_xboole_0(A_96, B_97)) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.99/4.94  tff(c_481, plain, (![A_19, B_97]: (k7_relat_1('#skF_2'(A_19), k3_xboole_0(A_19, B_97))=k7_relat_1('#skF_2'(A_19), B_97) | ~v1_relat_1('#skF_2'(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_455])).
% 11.99/4.94  tff(c_620, plain, (![A_104, B_105]: (k7_relat_1('#skF_2'(A_104), k3_xboole_0(A_104, B_105))=k7_relat_1('#skF_2'(A_104), B_105))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_481])).
% 11.99/4.94  tff(c_632, plain, (![A_104, B_105]: (k3_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k1_relat_1(k7_relat_1('#skF_2'(A_104), B_105)))), inference(superposition, [status(thm), theory('equality')], [c_620, c_170])).
% 11.99/4.94  tff(c_653, plain, (![A_106, B_107]: (k3_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_632])).
% 11.99/4.94  tff(c_682, plain, (![A_81]: (k3_xboole_0(k1_relat_1('#skF_4'), k1_relat_1(k7_relat_1('#skF_4', A_81)))=k3_xboole_0(k1_relat_1('#skF_4'), A_81))), inference(superposition, [status(thm), theory('equality')], [c_268, c_653])).
% 11.99/4.94  tff(c_703, plain, (![A_81]: (k3_xboole_0(k1_relat_1('#skF_4'), k1_relat_1(k7_relat_1('#skF_4', A_81)))=k1_relat_1(k7_relat_1('#skF_4', A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_682])).
% 11.99/4.94  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.99/4.94  tff(c_798, plain, (![A_112, C_113, B_114]: (r2_hidden(A_112, k1_relat_1(C_113)) | ~r2_hidden(A_112, k1_relat_1(k7_relat_1(C_113, B_114))) | ~v1_relat_1(C_113))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.99/4.94  tff(c_830, plain, (![A_112, A_19, A_81]: (r2_hidden(A_112, k1_relat_1('#skF_2'(A_19))) | ~r2_hidden(A_112, k3_xboole_0(A_19, A_81)) | ~v1_relat_1('#skF_2'(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_798])).
% 11.99/4.94  tff(c_863, plain, (![A_115, A_116, A_117]: (r2_hidden(A_115, A_116) | ~r2_hidden(A_115, k3_xboole_0(A_116, A_117)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_830])).
% 11.99/4.94  tff(c_1288, plain, (![A_138, A_139, B_140]: (r2_hidden('#skF_1'(k3_xboole_0(A_138, A_139), B_140), A_138) | r1_tarski(k3_xboole_0(A_138, A_139), B_140))), inference(resolution, [status(thm)], [c_6, c_863])).
% 11.99/4.94  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.99/4.94  tff(c_1351, plain, (![A_141, A_142]: (r1_tarski(k3_xboole_0(A_141, A_142), A_141))), inference(resolution, [status(thm)], [c_1288, c_4])).
% 11.99/4.94  tff(c_1354, plain, (![A_81]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_81)), k1_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_703, c_1351])).
% 11.99/4.94  tff(c_22, plain, (![A_18]: (k7_relat_1(A_18, k1_relat_1(A_18))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.99/4.94  tff(c_1505, plain, (![A_149, B_150]: (k7_relat_1(A_149, k3_xboole_0(k1_relat_1(A_149), B_150))=k7_relat_1(A_149, B_150) | ~v1_relat_1(A_149) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_22, c_455])).
% 11.99/4.94  tff(c_1593, plain, (![A_81]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', A_81)))=k7_relat_1('#skF_4', A_81) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_1505])).
% 11.99/4.94  tff(c_1643, plain, (![A_81]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', A_81)))=k7_relat_1('#skF_4', A_81))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_1593])).
% 11.99/4.94  tff(c_94, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_4'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_42, c_85])).
% 11.99/4.94  tff(c_101, plain, (k7_relat_1('#skF_5', k1_relat_1('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_94])).
% 11.99/4.94  tff(c_484, plain, (![B_97]: (k7_relat_1('#skF_5', k3_xboole_0(k1_relat_1('#skF_4'), B_97))=k7_relat_1('#skF_5', B_97) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_455])).
% 11.99/4.94  tff(c_497, plain, (![B_97]: (k7_relat_1('#skF_5', k1_relat_1(k7_relat_1('#skF_4', B_97)))=k7_relat_1('#skF_5', B_97))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_268, c_484])).
% 11.99/4.94  tff(c_1366, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1351])).
% 11.99/4.94  tff(c_1388, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_3'(A_144, B_145, C_146), C_146) | k7_relat_1(B_145, C_146)=k7_relat_1(A_144, C_146) | ~r1_tarski(C_146, k1_relat_1(B_145)) | ~r1_tarski(C_146, k1_relat_1(A_144)) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.99/4.94  tff(c_18, plain, (![A_13, B_14, C_15]: (r2_hidden(A_13, B_14) | ~r2_hidden(A_13, k1_relat_1(k7_relat_1(C_15, B_14))) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.99/4.94  tff(c_16057, plain, (![A_481, B_482, C_483, B_484]: (r2_hidden('#skF_3'(A_481, B_482, k1_relat_1(k7_relat_1(C_483, B_484))), B_484) | ~v1_relat_1(C_483) | k7_relat_1(B_482, k1_relat_1(k7_relat_1(C_483, B_484)))=k7_relat_1(A_481, k1_relat_1(k7_relat_1(C_483, B_484))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_483, B_484)), k1_relat_1(B_482)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_483, B_484)), k1_relat_1(A_481)) | ~v1_funct_1(B_482) | ~v1_relat_1(B_482) | ~v1_funct_1(A_481) | ~v1_relat_1(A_481))), inference(resolution, [status(thm)], [c_1388, c_18])).
% 11.99/4.94  tff(c_40, plain, (![D_58]: (k1_funct_1('#skF_5', D_58)=k1_funct_1('#skF_4', D_58) | ~r2_hidden(D_58, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.99/4.94  tff(c_16322, plain, (![A_485, B_486, C_487]: (k1_funct_1('#skF_5', '#skF_3'(A_485, B_486, k1_relat_1(k7_relat_1(C_487, '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'(A_485, B_486, k1_relat_1(k7_relat_1(C_487, '#skF_6')))) | ~v1_relat_1(C_487) | k7_relat_1(B_486, k1_relat_1(k7_relat_1(C_487, '#skF_6')))=k7_relat_1(A_485, k1_relat_1(k7_relat_1(C_487, '#skF_6'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_487, '#skF_6')), k1_relat_1(B_486)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_487, '#skF_6')), k1_relat_1(A_485)) | ~v1_funct_1(B_486) | ~v1_relat_1(B_486) | ~v1_funct_1(A_485) | ~v1_relat_1(A_485))), inference(resolution, [status(thm)], [c_16057, c_40])).
% 11.99/4.94  tff(c_20855, plain, (![A_590, B_591]: (k1_funct_1('#skF_5', '#skF_3'(A_590, B_591, k1_relat_1(k7_relat_1(B_591, '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'(A_590, B_591, k1_relat_1(k7_relat_1(B_591, '#skF_6')))) | k7_relat_1(B_591, k1_relat_1(k7_relat_1(B_591, '#skF_6')))=k7_relat_1(A_590, k1_relat_1(k7_relat_1(B_591, '#skF_6'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_591, '#skF_6')), k1_relat_1(A_590)) | ~v1_funct_1(B_591) | ~v1_funct_1(A_590) | ~v1_relat_1(A_590) | ~v1_relat_1(B_591))), inference(resolution, [status(thm)], [c_1366, c_16322])).
% 11.99/4.94  tff(c_20906, plain, (![B_591]: (k1_funct_1('#skF_5', '#skF_3'('#skF_5', B_591, k1_relat_1(k7_relat_1(B_591, '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'('#skF_5', B_591, k1_relat_1(k7_relat_1(B_591, '#skF_6')))) | k7_relat_1(B_591, k1_relat_1(k7_relat_1(B_591, '#skF_6')))=k7_relat_1('#skF_5', k1_relat_1(k7_relat_1(B_591, '#skF_6'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_591, '#skF_6')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_591) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(B_591))), inference(superposition, [status(thm), theory('equality')], [c_42, c_20855])).
% 11.99/4.94  tff(c_22108, plain, (![B_603]: (k1_funct_1('#skF_5', '#skF_3'('#skF_5', B_603, k1_relat_1(k7_relat_1(B_603, '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'('#skF_5', B_603, k1_relat_1(k7_relat_1(B_603, '#skF_6')))) | k7_relat_1(B_603, k1_relat_1(k7_relat_1(B_603, '#skF_6')))=k7_relat_1('#skF_5', k1_relat_1(k7_relat_1(B_603, '#skF_6'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_603, '#skF_6')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_20906])).
% 11.99/4.94  tff(c_22126, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_5', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'('#skF_5', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6')))) | k7_relat_1('#skF_5', k1_relat_1(k7_relat_1('#skF_4', '#skF_6')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1366, c_22108])).
% 11.99/4.94  tff(c_22152, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_5', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'('#skF_5', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6')))) | k7_relat_1('#skF_5', '#skF_6')=k7_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1643, c_497, c_22126])).
% 11.99/4.94  tff(c_22153, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_5', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6'))))=k1_funct_1('#skF_4', '#skF_3'('#skF_5', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_22152])).
% 11.99/4.94  tff(c_34, plain, (![B_37, A_25, C_43]: (k1_funct_1(B_37, '#skF_3'(A_25, B_37, C_43))!=k1_funct_1(A_25, '#skF_3'(A_25, B_37, C_43)) | k7_relat_1(B_37, C_43)=k7_relat_1(A_25, C_43) | ~r1_tarski(C_43, k1_relat_1(B_37)) | ~r1_tarski(C_43, k1_relat_1(A_25)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.99/4.94  tff(c_22570, plain, (k7_relat_1('#skF_5', k1_relat_1(k7_relat_1('#skF_4', '#skF_6')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_6'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_6')), k1_relat_1('#skF_4')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_6')), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22153, c_34])).
% 11.99/4.94  tff(c_22575, plain, (k7_relat_1('#skF_5', '#skF_6')=k7_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_50, c_48, c_1354, c_42, c_1354, c_1643, c_497, c_22570])).
% 11.99/4.94  tff(c_22577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_22575])).
% 11.99/4.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.99/4.94  
% 11.99/4.94  Inference rules
% 11.99/4.94  ----------------------
% 11.99/4.94  #Ref     : 2
% 11.99/4.94  #Sup     : 5263
% 11.99/4.94  #Fact    : 0
% 11.99/4.94  #Define  : 0
% 11.99/4.94  #Split   : 2
% 11.99/4.94  #Chain   : 0
% 11.99/4.94  #Close   : 0
% 11.99/4.94  
% 11.99/4.94  Ordering : KBO
% 11.99/4.94  
% 11.99/4.94  Simplification rules
% 11.99/4.94  ----------------------
% 11.99/4.94  #Subsume      : 1177
% 11.99/4.94  #Demod        : 7433
% 11.99/4.94  #Tautology    : 1457
% 11.99/4.94  #SimpNegUnit  : 4
% 11.99/4.94  #BackRed      : 16
% 11.99/4.94  
% 11.99/4.94  #Partial instantiations: 0
% 11.99/4.94  #Strategies tried      : 1
% 11.99/4.94  
% 11.99/4.94  Timing (in seconds)
% 11.99/4.94  ----------------------
% 11.99/4.95  Preprocessing        : 0.33
% 11.99/4.95  Parsing              : 0.17
% 11.99/4.95  CNF conversion       : 0.02
% 11.99/4.95  Main loop            : 3.82
% 11.99/4.95  Inferencing          : 0.86
% 11.99/4.95  Reduction            : 1.74
% 11.99/4.95  Demodulation         : 1.48
% 11.99/4.95  BG Simplification    : 0.12
% 11.99/4.95  Subsumption          : 0.92
% 11.99/4.95  Abstraction          : 0.21
% 11.99/4.95  MUC search           : 0.00
% 11.99/4.95  Cooper               : 0.00
% 11.99/4.95  Total                : 4.19
% 11.99/4.95  Index Insertion      : 0.00
% 11.99/4.95  Index Deletion       : 0.00
% 11.99/4.95  Index Matching       : 0.00
% 11.99/4.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
