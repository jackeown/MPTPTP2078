%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:09 EST 2020

% Result     : Theorem 15.34s
% Output     : CNFRefutation 15.34s
% Verified   : 
% Statistics : Number of formulae       :  219 (2080 expanded)
%              Number of leaves         :   25 ( 707 expanded)
%              Depth                    :   21
%              Number of atoms          :  453 (6136 expanded)
%              Number of equality atoms :  161 (2745 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_73,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    ! [A_49,B_50] : k1_relat_1('#skF_6'(A_49,B_50)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [A_49,B_50] : v1_relat_1('#skF_6'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_61,plain,(
    ! [A_65] :
      ( k1_relat_1(A_65) != k1_xboole_0
      | k1_xboole_0 = A_65
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_49,B_50] :
      ( k1_relat_1('#skF_6'(A_49,B_50)) != k1_xboole_0
      | '#skF_6'(A_49,B_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_66,plain,(
    ! [A_49,B_50] :
      ( k1_xboole_0 != A_49
      | '#skF_6'(A_49,B_50) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_49,B_50] : v1_funct_1('#skF_6'(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_267,plain,(
    ! [A_106,C_107] :
      ( r2_hidden('#skF_5'(A_106,k2_relat_1(A_106),C_107),k1_relat_1(A_106))
      | ~ r2_hidden(C_107,k2_relat_1(A_106))
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_276,plain,(
    ! [A_49,B_50,C_107] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_107),A_49)
      | ~ r2_hidden(C_107,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_267])).

tff(c_7571,plain,(
    ! [A_2253,B_2254,C_2255] :
      ( r2_hidden('#skF_5'('#skF_6'(A_2253,B_2254),k2_relat_1('#skF_6'(A_2253,B_2254)),C_2255),A_2253)
      | ~ r2_hidden(C_2255,k2_relat_1('#skF_6'(A_2253,B_2254))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_276])).

tff(c_36,plain,(
    ! [A_49,B_50,D_55] :
      ( k1_funct_1('#skF_6'(A_49,B_50),D_55) = B_50
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_163,plain,(
    ! [A_89,D_90] :
      ( r2_hidden(k1_funct_1(A_89,D_90),k2_relat_1(A_89))
      | ~ r2_hidden(D_90,k1_relat_1(A_89))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_170,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,k1_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_163])).

tff(c_174,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_170])).

tff(c_7995,plain,(
    ! [B_2290,A_2291,C_2292,B_2293] :
      ( r2_hidden(B_2290,k2_relat_1('#skF_6'(A_2291,B_2290)))
      | ~ r2_hidden(C_2292,k2_relat_1('#skF_6'(A_2291,B_2293))) ) ),
    inference(resolution,[status(thm)],[c_7571,c_174])).

tff(c_8091,plain,(
    ! [B_2290,A_49,C_2292] :
      ( r2_hidden(B_2290,k2_relat_1('#skF_6'(A_49,B_2290)))
      | ~ r2_hidden(C_2292,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_7995])).

tff(c_9534,plain,(
    ! [C_2696] : ~ r2_hidden(C_2696,k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8091])).

tff(c_9605,plain,(
    ! [B_2766] : r1_tarski(k2_relat_1(k1_xboole_0),B_2766) ),
    inference(resolution,[status(thm)],[c_6,c_9534])).

tff(c_175,plain,(
    ! [B_91,A_92,D_93] :
      ( r2_hidden(B_91,k2_relat_1('#skF_6'(A_92,B_91)))
      | ~ r2_hidden(D_93,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_170])).

tff(c_182,plain,(
    ! [B_94,A_95,B_96] :
      ( r2_hidden(B_94,k2_relat_1('#skF_6'(A_95,B_94)))
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_194,plain,(
    ! [B_50,A_49,B_96] :
      ( r2_hidden(B_50,k2_relat_1(k1_xboole_0))
      | r1_tarski(A_49,B_96)
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_182])).

tff(c_225,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(A_99,B_100)
      | k1_xboole_0 != A_99 ) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_232,plain,(
    ! [B_100,A_99] :
      ( B_100 = A_99
      | ~ r1_tarski(B_100,A_99)
      | k1_xboole_0 != A_99 ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_9715,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9605,c_232])).

tff(c_68,plain,(
    ! [A_66,B_67] :
      ( k1_xboole_0 != A_66
      | '#skF_6'(A_66,B_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_78,plain,(
    ! [A_66] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_40])).

tff(c_98,plain,(
    ! [A_66] : k1_xboole_0 != A_66 ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_104,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_98])).

tff(c_105,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_116,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_38])).

tff(c_76,plain,(
    ! [A_66] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_42])).

tff(c_84,plain,(
    ! [A_66] : k1_xboole_0 != A_66 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_91,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_84])).

tff(c_92,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_44,plain,(
    ! [C_57] :
      ( ~ r1_tarski(k2_relat_1(C_57),'#skF_7')
      | k1_relat_1(C_57) != '#skF_8'
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_253,plain,(
    ! [C_105] :
      ( k1_relat_1(C_105) != '#skF_8'
      | ~ v1_funct_1(C_105)
      | ~ v1_relat_1(C_105)
      | k2_relat_1(C_105) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_225,c_44])).

tff(c_256,plain,
    ( k1_relat_1(k1_xboole_0) != '#skF_8'
    | ~ v1_funct_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_253])).

tff(c_262,plain,
    ( k1_xboole_0 != '#skF_8'
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_116,c_256])).

tff(c_266,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_9721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9715,c_266])).

tff(c_9724,plain,(
    ! [B_2801,A_2802] :
      ( r2_hidden(B_2801,k2_relat_1('#skF_6'(A_2802,B_2801)))
      | k1_xboole_0 != A_2802 ) ),
    inference(splitRight,[status(thm)],[c_8091])).

tff(c_9941,plain,(
    ! [B_50,A_49] :
      ( r2_hidden(B_50,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_9724])).

tff(c_10249,plain,(
    ! [A_49] :
      ( k1_xboole_0 != A_49
      | k1_xboole_0 != A_49 ) ),
    inference(splitLeft,[status(thm)],[c_9941])).

tff(c_10255,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10249])).

tff(c_10256,plain,(
    ! [B_50] : r2_hidden(B_50,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_9941])).

tff(c_281,plain,(
    ! [A_49,B_50,C_107] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_107),A_49)
      | ~ r2_hidden(C_107,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_276])).

tff(c_200,plain,(
    ! [A_97,C_98] :
      ( k1_funct_1(A_97,'#skF_5'(A_97,k2_relat_1(A_97),C_98)) = C_98
      | ~ r2_hidden(C_98,k2_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_210,plain,(
    ! [C_98,B_50,A_49] :
      ( C_98 = B_50
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_98),A_49)
      | ~ r2_hidden(C_98,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_36])).

tff(c_9947,plain,(
    ! [C_2837,B_2838,A_2839] :
      ( C_2837 = B_2838
      | ~ r2_hidden('#skF_5'('#skF_6'(A_2839,B_2838),k2_relat_1('#skF_6'(A_2839,B_2838)),C_2837),A_2839)
      | ~ r2_hidden(C_2837,k2_relat_1('#skF_6'(A_2839,B_2838))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_210])).

tff(c_9982,plain,(
    ! [C_2874,B_2875,A_2876] :
      ( C_2874 = B_2875
      | ~ r2_hidden(C_2874,k2_relat_1('#skF_6'(A_2876,B_2875))) ) ),
    inference(resolution,[status(thm)],[c_281,c_9947])).

tff(c_10061,plain,(
    ! [C_2874,B_50,A_49] :
      ( C_2874 = B_50
      | ~ r2_hidden(C_2874,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_9982])).

tff(c_10095,plain,(
    ! [A_49] : k1_xboole_0 != A_49 ),
    inference(splitLeft,[status(thm)],[c_10061])).

tff(c_10111,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10095])).

tff(c_10112,plain,(
    ! [C_2874,B_50] :
      ( C_2874 = B_50
      | ~ r2_hidden(C_2874,k2_relat_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_10061])).

tff(c_10872,plain,(
    ! [C_3093,B_3094] : C_3093 = B_3094 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10256,c_10112])).

tff(c_14718,plain,(
    ! [B_3094] : B_3094 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_10872,c_49])).

tff(c_15100,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_14718])).

tff(c_15102,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_67,plain,(
    ! [B_50] : '#skF_6'(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_18,plain,(
    ! [A_9,D_48] :
      ( r2_hidden(k1_funct_1(A_9,D_48),k2_relat_1(A_9))
      | ~ r2_hidden(D_48,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15113,plain,(
    ! [D_48] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_48),k1_xboole_0)
      | ~ r2_hidden(D_48,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15102,c_18])).

tff(c_15133,plain,(
    ! [D_4699] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_4699),k1_xboole_0)
      | ~ r2_hidden(D_4699,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_105,c_116,c_15113])).

tff(c_15135,plain,(
    ! [B_50,D_4699] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(k1_xboole_0,B_50)))
      | ~ r2_hidden(D_4699,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_15133,c_174])).

tff(c_15145,plain,(
    ! [B_50,D_4699] :
      ( r2_hidden(B_50,k1_xboole_0)
      | ~ r2_hidden(D_4699,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15102,c_67,c_15135])).

tff(c_15152,plain,(
    ! [D_4699] : ~ r2_hidden(D_4699,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_15145])).

tff(c_15161,plain,(
    ! [A_4701,C_4702] :
      ( r2_hidden('#skF_5'(A_4701,k2_relat_1(A_4701),C_4702),k1_relat_1(A_4701))
      | ~ r2_hidden(C_4702,k2_relat_1(A_4701))
      | ~ v1_funct_1(A_4701)
      | ~ v1_relat_1(A_4701) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_23336,plain,(
    ! [B_7089,A_7090,C_7091] :
      ( r2_hidden(B_7089,k2_relat_1('#skF_6'(k1_relat_1(A_7090),B_7089)))
      | ~ r2_hidden(C_7091,k2_relat_1(A_7090))
      | ~ v1_funct_1(A_7090)
      | ~ v1_relat_1(A_7090) ) ),
    inference(resolution,[status(thm)],[c_15161,c_174])).

tff(c_24542,plain,(
    ! [B_7492,A_7493,B_7494] :
      ( r2_hidden(B_7492,k2_relat_1('#skF_6'(k1_relat_1(A_7493),B_7492)))
      | ~ v1_funct_1(A_7493)
      | ~ v1_relat_1(A_7493)
      | r1_tarski(k2_relat_1(A_7493),B_7494) ) ),
    inference(resolution,[status(thm)],[c_6,c_23336])).

tff(c_25007,plain,(
    ! [B_7492,A_49,B_50,B_7494] :
      ( r2_hidden(B_7492,k2_relat_1('#skF_6'(A_49,B_7492)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | r1_tarski(k2_relat_1('#skF_6'(A_49,B_50)),B_7494) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_24542])).

tff(c_25211,plain,(
    ! [B_7565,A_7566,B_7567,B_7568] :
      ( r2_hidden(B_7565,k2_relat_1('#skF_6'(A_7566,B_7565)))
      | r1_tarski(k2_relat_1('#skF_6'(A_7566,B_7567)),B_7568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_25007])).

tff(c_25671,plain,(
    ! [B_50,A_49,B_7567,B_7568] :
      ( r2_hidden(B_50,k2_relat_1(k1_xboole_0))
      | r1_tarski(k2_relat_1('#skF_6'(A_49,B_7567)),B_7568)
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_25211])).

tff(c_25699,plain,(
    ! [B_50,A_49,B_7567,B_7568] :
      ( r2_hidden(B_50,k1_xboole_0)
      | r1_tarski(k2_relat_1('#skF_6'(A_49,B_7567)),B_7568)
      | k1_xboole_0 != A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15102,c_25671])).

tff(c_26073,plain,(
    ! [A_7676,B_7677,B_7678] :
      ( r1_tarski(k2_relat_1('#skF_6'(A_7676,B_7677)),B_7678)
      | k1_xboole_0 != A_7676 ) ),
    inference(negUnitSimplification,[status(thm)],[c_15152,c_25699])).

tff(c_26332,plain,(
    ! [A_7676,B_7677,B_7678] :
      ( k2_relat_1('#skF_6'(A_7676,B_7677)) = B_7678
      | k1_xboole_0 != B_7678
      | k1_xboole_0 != A_7676 ) ),
    inference(resolution,[status(thm)],[c_26073,c_232])).

tff(c_26393,plain,(
    ! [B_7677] : k2_relat_1('#skF_6'(k1_xboole_0,B_7677)) = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_26332])).

tff(c_15292,plain,(
    ! [A_4726,B_4727] :
      ( r2_hidden('#skF_3'(A_4726,B_4727),k1_relat_1(A_4726))
      | r2_hidden('#skF_4'(A_4726,B_4727),B_4727)
      | k2_relat_1(A_4726) = B_4727
      | ~ v1_funct_1(A_4726)
      | ~ v1_relat_1(A_4726) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15309,plain,(
    ! [A_49,B_50,B_4727] :
      ( r2_hidden('#skF_3'('#skF_6'(A_49,B_50),B_4727),A_49)
      | r2_hidden('#skF_4'('#skF_6'(A_49,B_50),B_4727),B_4727)
      | k2_relat_1('#skF_6'(A_49,B_50)) = B_4727
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_15292])).

tff(c_30296,plain,(
    ! [A_8710,B_8711,B_8712] :
      ( r2_hidden('#skF_3'('#skF_6'(A_8710,B_8711),B_8712),A_8710)
      | r2_hidden('#skF_4'('#skF_6'(A_8710,B_8711),B_8712),B_8712)
      | k2_relat_1('#skF_6'(A_8710,B_8711)) = B_8712 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_15309])).

tff(c_30338,plain,(
    ! [B_8711,B_8712] :
      ( r2_hidden('#skF_4'('#skF_6'(k1_xboole_0,B_8711),B_8712),B_8712)
      | k2_relat_1('#skF_6'(k1_xboole_0,B_8711)) = B_8712 ) ),
    inference(resolution,[status(thm)],[c_30296,c_15152])).

tff(c_30861,plain,(
    ! [B_8712] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_8712),B_8712)
      | k1_xboole_0 = B_8712 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26393,c_67,c_30338])).

tff(c_15173,plain,(
    ! [A_49,B_50,C_4702] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_4702),A_49)
      | ~ r2_hidden(C_4702,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_15161])).

tff(c_15181,plain,(
    ! [A_49,B_50,C_4702] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_4702),A_49)
      | ~ r2_hidden(C_4702,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_15173])).

tff(c_28625,plain,(
    ! [C_8377,B_8378,A_8379] :
      ( C_8377 = B_8378
      | ~ r2_hidden('#skF_5'('#skF_6'(A_8379,B_8378),k2_relat_1('#skF_6'(A_8379,B_8378)),C_8377),A_8379)
      | ~ r2_hidden(C_8377,k2_relat_1('#skF_6'(A_8379,B_8378))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_210])).

tff(c_28664,plain,(
    ! [C_8414,B_8415,A_8416] :
      ( C_8414 = B_8415
      | ~ r2_hidden(C_8414,k2_relat_1('#skF_6'(A_8416,B_8415))) ) ),
    inference(resolution,[status(thm)],[c_15181,c_28625])).

tff(c_53282,plain,(
    ! [A_11759,B_11760,B_11761] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_11759,B_11760)),B_11761) = B_11760
      | r1_tarski(k2_relat_1('#skF_6'(A_11759,B_11760)),B_11761) ) ),
    inference(resolution,[status(thm)],[c_6,c_28664])).

tff(c_53425,plain,(
    ! [A_11759,B_11760] :
      ( k1_relat_1('#skF_6'(A_11759,B_11760)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_11759,B_11760))
      | ~ v1_relat_1('#skF_6'(A_11759,B_11760))
      | '#skF_1'(k2_relat_1('#skF_6'(A_11759,B_11760)),'#skF_7') = B_11760 ) ),
    inference(resolution,[status(thm)],[c_53282,c_44])).

tff(c_53813,plain,(
    ! [A_11796,B_11797] :
      ( A_11796 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_11796,B_11797)),'#skF_7') = B_11797 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_53425])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54615,plain,(
    ! [B_11868,A_11869] :
      ( ~ r2_hidden(B_11868,'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(A_11869,B_11868)),'#skF_7')
      | A_11869 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53813,c_4])).

tff(c_54656,plain,(
    ! [A_11869,B_11868] :
      ( k1_relat_1('#skF_6'(A_11869,B_11868)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_11869,B_11868))
      | ~ v1_relat_1('#skF_6'(A_11869,B_11868))
      | ~ r2_hidden(B_11868,'#skF_7')
      | A_11869 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_54615,c_44])).

tff(c_54948,plain,(
    ! [B_11868,A_11869] :
      ( ~ r2_hidden(B_11868,'#skF_7')
      | A_11869 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54656])).

tff(c_54962,plain,(
    ! [A_11869] : A_11869 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_54948])).

tff(c_54966,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_54962])).

tff(c_54968,plain,(
    ! [B_11904] : ~ r2_hidden(B_11904,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_54948])).

tff(c_54992,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_30861,c_54968])).

tff(c_55030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_54992])).

tff(c_55034,plain,(
    ! [B_11939] : r2_hidden(B_11939,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_15145])).

tff(c_55072,plain,(
    ! [A_11942] : r1_tarski(A_11942,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_55034,c_4])).

tff(c_55082,plain,(
    ! [A_11943] : k1_xboole_0 = A_11943 ),
    inference(resolution,[status(thm)],[c_55072,c_232])).

tff(c_55127,plain,(
    ! [A_11943] : A_11943 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_55082,c_49])).

tff(c_55145,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_55127])).

tff(c_55146,plain,(
    ! [B_50] : r2_hidden(B_50,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_55261,plain,(
    ! [A_12311,C_12312] :
      ( r2_hidden('#skF_5'(A_12311,k2_relat_1(A_12311),C_12312),k1_relat_1(A_12311))
      | ~ r2_hidden(C_12312,k2_relat_1(A_12311))
      | ~ v1_funct_1(A_12311)
      | ~ v1_relat_1(A_12311) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55270,plain,(
    ! [A_49,B_50,C_12312] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_12312),A_49)
      | ~ r2_hidden(C_12312,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_55261])).

tff(c_55275,plain,(
    ! [A_49,B_50,C_12312] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_12312),A_49)
      | ~ r2_hidden(C_12312,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_55270])).

tff(c_55182,plain,(
    ! [A_12304,C_12305] :
      ( k1_funct_1(A_12304,'#skF_5'(A_12304,k2_relat_1(A_12304),C_12305)) = C_12305
      | ~ r2_hidden(C_12305,k2_relat_1(A_12304))
      | ~ v1_funct_1(A_12304)
      | ~ v1_relat_1(A_12304) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55192,plain,(
    ! [C_12305,B_50,A_49] :
      ( C_12305 = B_50
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_12305),A_49)
      | ~ r2_hidden(C_12305,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55182,c_36])).

tff(c_56649,plain,(
    ! [C_13296,B_13297,A_13298] :
      ( C_13296 = B_13297
      | ~ r2_hidden('#skF_5'('#skF_6'(A_13298,B_13297),k2_relat_1('#skF_6'(A_13298,B_13297)),C_13296),A_13298)
      | ~ r2_hidden(C_13296,k2_relat_1('#skF_6'(A_13298,B_13297))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_55192])).

tff(c_56665,plain,(
    ! [C_13299,B_13300,A_13301] :
      ( C_13299 = B_13300
      | ~ r2_hidden(C_13299,k2_relat_1('#skF_6'(A_13301,B_13300))) ) ),
    inference(resolution,[status(thm)],[c_55275,c_56649])).

tff(c_56729,plain,(
    ! [C_13299,B_50,A_49] :
      ( C_13299 = B_50
      | ~ r2_hidden(C_13299,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_56665])).

tff(c_56762,plain,(
    ! [C_13299,B_50,A_49] :
      ( C_13299 = B_50
      | k1_xboole_0 != A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55146,c_56729])).

tff(c_56763,plain,(
    ! [A_49] : k1_xboole_0 != A_49 ),
    inference(splitLeft,[status(thm)],[c_56762])).

tff(c_56776,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_56763])).

tff(c_56813,plain,(
    ! [C_13305,B_13306] : C_13305 = B_13306 ),
    inference(splitRight,[status(thm)],[c_56762])).

tff(c_61741,plain,(
    ! [B_13306] : B_13306 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_56813,c_49])).

tff(c_62099,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_61741])).

tff(c_62100,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62125,plain,(
    ! [A_15051] :
      ( k1_relat_1(A_15051) != '#skF_8'
      | A_15051 = '#skF_8'
      | ~ v1_relat_1(A_15051) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62100,c_62100,c_16])).

tff(c_62128,plain,(
    ! [A_49,B_50] :
      ( k1_relat_1('#skF_6'(A_49,B_50)) != '#skF_8'
      | '#skF_6'(A_49,B_50) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_62125])).

tff(c_62138,plain,(
    ! [A_15053,B_15054] :
      ( A_15053 != '#skF_8'
      | '#skF_6'(A_15053,B_15054) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62128])).

tff(c_62148,plain,(
    ! [A_15053] :
      ( v1_relat_1('#skF_8')
      | A_15053 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62138,c_42])).

tff(c_62163,plain,(
    ! [A_15053] : A_15053 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_62148])).

tff(c_62101,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_62107,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62100,c_62101])).

tff(c_62169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62163,c_62107])).

tff(c_62170,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_62148])).

tff(c_62146,plain,(
    ! [A_15053] :
      ( v1_funct_1('#skF_8')
      | A_15053 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62138,c_40])).

tff(c_62154,plain,(
    ! [A_15053] : A_15053 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_62146])).

tff(c_62160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62154,c_62107])).

tff(c_62161,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_62146])).

tff(c_62181,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_62138,c_38])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62130,plain,(
    ! [A_49,B_50] :
      ( A_49 != '#skF_8'
      | '#skF_6'(A_49,B_50) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62128])).

tff(c_62675,plain,(
    ! [A_15558,C_15559] :
      ( r2_hidden('#skF_5'(A_15558,k2_relat_1(A_15558),C_15559),k1_relat_1(A_15558))
      | ~ r2_hidden(C_15559,k2_relat_1(A_15558))
      | ~ v1_funct_1(A_15558)
      | ~ v1_relat_1(A_15558) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62684,plain,(
    ! [A_49,B_50,C_15559] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_15559),A_49)
      | ~ r2_hidden(C_15559,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_62675])).

tff(c_63020,plain,(
    ! [A_15645,B_15646,C_15647] :
      ( r2_hidden('#skF_5'('#skF_6'(A_15645,B_15646),k2_relat_1('#skF_6'(A_15645,B_15646)),C_15647),A_15645)
      | ~ r2_hidden(C_15647,k2_relat_1('#skF_6'(A_15645,B_15646))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62684])).

tff(c_62493,plain,(
    ! [A_15490,D_15491] :
      ( r2_hidden(k1_funct_1(A_15490,D_15491),k2_relat_1(A_15490))
      | ~ r2_hidden(D_15491,k1_relat_1(A_15490))
      | ~ v1_funct_1(A_15490)
      | ~ v1_relat_1(A_15490) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62564,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,k1_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62493])).

tff(c_62592,plain,(
    ! [B_50,A_49,D_55] :
      ( r2_hidden(B_50,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ r2_hidden(D_55,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_62564])).

tff(c_63036,plain,(
    ! [B_15648,A_15649,C_15650,B_15651] :
      ( r2_hidden(B_15648,k2_relat_1('#skF_6'(A_15649,B_15648)))
      | ~ r2_hidden(C_15650,k2_relat_1('#skF_6'(A_15649,B_15651))) ) ),
    inference(resolution,[status(thm)],[c_63020,c_62592])).

tff(c_63077,plain,(
    ! [B_15652,A_15653,B_15654,B_15655] :
      ( r2_hidden(B_15652,k2_relat_1('#skF_6'(A_15653,B_15652)))
      | r1_tarski(k2_relat_1('#skF_6'(A_15653,B_15654)),B_15655) ) ),
    inference(resolution,[status(thm)],[c_6,c_63036])).

tff(c_62108,plain,(
    ! [C_57] :
      ( ~ r1_tarski(k2_relat_1(C_57),'#skF_8')
      | k1_relat_1(C_57) != '#skF_8'
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62107,c_44])).

tff(c_63111,plain,(
    ! [A_15653,B_15654,B_15652] :
      ( k1_relat_1('#skF_6'(A_15653,B_15654)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_15653,B_15654))
      | ~ v1_relat_1('#skF_6'(A_15653,B_15654))
      | r2_hidden(B_15652,k2_relat_1('#skF_6'(A_15653,B_15652))) ) ),
    inference(resolution,[status(thm)],[c_63077,c_62108])).

tff(c_63136,plain,(
    ! [A_15656,B_15657] :
      ( A_15656 != '#skF_8'
      | r2_hidden(B_15657,k2_relat_1('#skF_6'(A_15656,B_15657))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_63111])).

tff(c_63147,plain,(
    ! [A_49,B_50] :
      ( A_49 != '#skF_8'
      | r2_hidden(B_50,k2_relat_1('#skF_8'))
      | A_49 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62130,c_63136])).

tff(c_63152,plain,(
    ! [A_49] :
      ( A_49 != '#skF_8'
      | A_49 != '#skF_8' ) ),
    inference(splitLeft,[status(thm)],[c_63147])).

tff(c_63158,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_63152])).

tff(c_63159,plain,(
    ! [B_50] : r2_hidden(B_50,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_63147])).

tff(c_62689,plain,(
    ! [A_49,B_50,C_15559] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_15559),A_49)
      | ~ r2_hidden(C_15559,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62684])).

tff(c_62754,plain,(
    ! [A_15574,C_15575] :
      ( k1_funct_1(A_15574,'#skF_5'(A_15574,k2_relat_1(A_15574),C_15575)) = C_15575
      | ~ r2_hidden(C_15575,k2_relat_1(A_15574))
      | ~ v1_funct_1(A_15574)
      | ~ v1_relat_1(A_15574) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62764,plain,(
    ! [C_15575,B_50,A_49] :
      ( C_15575 = B_50
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_15575),A_49)
      | ~ r2_hidden(C_15575,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62754,c_36])).

tff(c_63431,plain,(
    ! [C_15681,B_15682,A_15683] :
      ( C_15681 = B_15682
      | ~ r2_hidden('#skF_5'('#skF_6'(A_15683,B_15682),k2_relat_1('#skF_6'(A_15683,B_15682)),C_15681),A_15683)
      | ~ r2_hidden(C_15681,k2_relat_1('#skF_6'(A_15683,B_15682))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62764])).

tff(c_63447,plain,(
    ! [C_15684,B_15685,A_15686] :
      ( C_15684 = B_15685
      | ~ r2_hidden(C_15684,k2_relat_1('#skF_6'(A_15686,B_15685))) ) ),
    inference(resolution,[status(thm)],[c_62689,c_63431])).

tff(c_63502,plain,(
    ! [C_15684,B_50,A_49] :
      ( C_15684 = B_50
      | ~ r2_hidden(C_15684,k2_relat_1('#skF_8'))
      | A_49 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62130,c_63447])).

tff(c_63529,plain,(
    ! [C_15684,B_50,A_49] :
      ( C_15684 = B_50
      | A_49 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63159,c_63502])).

tff(c_63530,plain,(
    ! [A_49] : A_49 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_63529])).

tff(c_63541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63530,c_62107])).

tff(c_63571,plain,(
    ! [C_15690,B_15691] : C_15690 = B_15691 ),
    inference(splitRight,[status(thm)],[c_63529])).

tff(c_62593,plain,(
    ! [B_15509,A_15510,D_15511] :
      ( r2_hidden(B_15509,k2_relat_1('#skF_6'(A_15510,B_15509)))
      | ~ r2_hidden(D_15511,A_15510) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_62564])).

tff(c_62603,plain,(
    ! [B_15529,A_15530,B_15531] :
      ( r2_hidden(B_15529,k2_relat_1('#skF_6'(A_15530,B_15529)))
      | r1_tarski(A_15530,B_15531) ) ),
    inference(resolution,[status(thm)],[c_6,c_62593])).

tff(c_62619,plain,(
    ! [B_50,A_49,B_15531] :
      ( r2_hidden(B_50,k2_relat_1('#skF_8'))
      | r1_tarski(A_49,B_15531)
      | A_49 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62130,c_62603])).

tff(c_62647,plain,(
    ! [A_15552,B_15553] :
      ( r1_tarski(A_15552,B_15553)
      | A_15552 != '#skF_8' ) ),
    inference(splitLeft,[status(thm)],[c_62619])).

tff(c_62690,plain,(
    ! [C_15560] :
      ( k1_relat_1(C_15560) != '#skF_8'
      | ~ v1_funct_1(C_15560)
      | ~ v1_relat_1(C_15560)
      | k2_relat_1(C_15560) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_62647,c_62108])).

tff(c_62693,plain,
    ( k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | k2_relat_1('#skF_8') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_62170,c_62690])).

tff(c_62699,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62161,c_62181,c_62693])).

tff(c_66655,plain,(
    ! [C_15690] : C_15690 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_63571,c_62699])).

tff(c_68024,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_66655])).

tff(c_68025,plain,(
    ! [B_50] : r2_hidden(B_50,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_62619])).

tff(c_68064,plain,(
    ! [A_17242,C_17243] :
      ( r2_hidden('#skF_5'(A_17242,k2_relat_1(A_17242),C_17243),k1_relat_1(A_17242))
      | ~ r2_hidden(C_17243,k2_relat_1(A_17242))
      | ~ v1_funct_1(A_17242)
      | ~ v1_relat_1(A_17242) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68079,plain,(
    ! [A_49,B_50,C_17243] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_17243),A_49)
      | ~ r2_hidden(C_17243,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_68064])).

tff(c_68084,plain,(
    ! [A_49,B_50,C_17243] :
      ( r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_17243),A_49)
      | ~ r2_hidden(C_17243,k2_relat_1('#skF_6'(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_68079])).

tff(c_68208,plain,(
    ! [A_17390,C_17391] :
      ( k1_funct_1(A_17390,'#skF_5'(A_17390,k2_relat_1(A_17390),C_17391)) = C_17391
      | ~ r2_hidden(C_17391,k2_relat_1(A_17390))
      | ~ v1_funct_1(A_17390)
      | ~ v1_relat_1(A_17390) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68243,plain,(
    ! [C_17391,B_50,A_49] :
      ( C_17391 = B_50
      | ~ r2_hidden(C_17391,k2_relat_1('#skF_6'(A_49,B_50)))
      | ~ v1_funct_1('#skF_6'(A_49,B_50))
      | ~ v1_relat_1('#skF_6'(A_49,B_50))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_49,B_50),k2_relat_1('#skF_6'(A_49,B_50)),C_17391),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_68208])).

tff(c_69803,plain,(
    ! [C_17723,B_17724,A_17725] :
      ( C_17723 = B_17724
      | ~ r2_hidden(C_17723,k2_relat_1('#skF_6'(A_17725,B_17724)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_17725,B_17724),k2_relat_1('#skF_6'(A_17725,B_17724)),C_17723),A_17725) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_68243])).

tff(c_69819,plain,(
    ! [C_17726,B_17727,A_17728] :
      ( C_17726 = B_17727
      | ~ r2_hidden(C_17726,k2_relat_1('#skF_6'(A_17728,B_17727))) ) ),
    inference(resolution,[status(thm)],[c_68084,c_69803])).

tff(c_69853,plain,(
    ! [C_17726,B_50,A_49] :
      ( C_17726 = B_50
      | ~ r2_hidden(C_17726,k2_relat_1('#skF_8'))
      | A_49 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62130,c_69819])).

tff(c_69866,plain,(
    ! [C_17726,B_50,A_49] :
      ( C_17726 = B_50
      | A_49 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68025,c_69853])).

tff(c_69867,plain,(
    ! [A_49] : A_49 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_69866])).

tff(c_69874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69867,c_62107])).

tff(c_69907,plain,(
    ! [C_17732,B_17733] : C_17732 = B_17733 ),
    inference(splitRight,[status(thm)],[c_69866])).

tff(c_68026,plain,(
    ! [B_17188] : r2_hidden(B_17188,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_62619])).

tff(c_62202,plain,(
    ! [A_15063,B_15064,D_15065] :
      ( k1_funct_1('#skF_6'(A_15063,B_15064),D_15065) = B_15064
      | ~ r2_hidden(D_15065,A_15063) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62211,plain,(
    ! [D_15065,B_50,A_49] :
      ( k1_funct_1('#skF_8',D_15065) = B_50
      | ~ r2_hidden(D_15065,A_49)
      | A_49 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62130,c_62202])).

tff(c_68038,plain,(
    ! [B_17188,B_50] :
      ( k1_funct_1('#skF_8',B_17188) = B_50
      | k2_relat_1('#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_68026,c_62211])).

tff(c_68085,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_68038])).

tff(c_70667,plain,(
    ! [B_17733] : B_17733 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_69907,c_68085])).

tff(c_72190,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_70667])).

tff(c_72192,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68038])).

tff(c_72206,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_72192,c_62108])).

tff(c_72215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62170,c_62161,c_62181,c_12,c_72206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.34/6.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.34/6.54  
% 15.34/6.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.34/6.54  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 15.34/6.54  
% 15.34/6.54  %Foreground sorts:
% 15.34/6.54  
% 15.34/6.54  
% 15.34/6.54  %Background operators:
% 15.34/6.54  
% 15.34/6.54  
% 15.34/6.54  %Foreground operators:
% 15.34/6.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 15.34/6.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.34/6.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.34/6.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.34/6.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.34/6.54  tff('#skF_7', type, '#skF_7': $i).
% 15.34/6.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.34/6.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.34/6.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.34/6.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 15.34/6.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.34/6.54  tff('#skF_8', type, '#skF_8': $i).
% 15.34/6.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.34/6.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.34/6.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.34/6.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.34/6.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.34/6.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.34/6.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.34/6.54  
% 15.34/6.57  tff(f_73, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 15.34/6.57  tff(f_91, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 15.34/6.57  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 15.34/6.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 15.34/6.57  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 15.34/6.57  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.34/6.57  tff(c_38, plain, (![A_49, B_50]: (k1_relat_1('#skF_6'(A_49, B_50))=A_49)), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.34/6.57  tff(c_42, plain, (![A_49, B_50]: (v1_relat_1('#skF_6'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.34/6.57  tff(c_46, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.34/6.57  tff(c_49, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_46])).
% 15.34/6.57  tff(c_61, plain, (![A_65]: (k1_relat_1(A_65)!=k1_xboole_0 | k1_xboole_0=A_65 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.34/6.57  tff(c_64, plain, (![A_49, B_50]: (k1_relat_1('#skF_6'(A_49, B_50))!=k1_xboole_0 | '#skF_6'(A_49, B_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_61])).
% 15.34/6.57  tff(c_66, plain, (![A_49, B_50]: (k1_xboole_0!=A_49 | '#skF_6'(A_49, B_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_64])).
% 15.34/6.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.34/6.57  tff(c_40, plain, (![A_49, B_50]: (v1_funct_1('#skF_6'(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.34/6.57  tff(c_267, plain, (![A_106, C_107]: (r2_hidden('#skF_5'(A_106, k2_relat_1(A_106), C_107), k1_relat_1(A_106)) | ~r2_hidden(C_107, k2_relat_1(A_106)) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_276, plain, (![A_49, B_50, C_107]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_107), A_49) | ~r2_hidden(C_107, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_267])).
% 15.34/6.57  tff(c_7571, plain, (![A_2253, B_2254, C_2255]: (r2_hidden('#skF_5'('#skF_6'(A_2253, B_2254), k2_relat_1('#skF_6'(A_2253, B_2254)), C_2255), A_2253) | ~r2_hidden(C_2255, k2_relat_1('#skF_6'(A_2253, B_2254))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_276])).
% 15.34/6.57  tff(c_36, plain, (![A_49, B_50, D_55]: (k1_funct_1('#skF_6'(A_49, B_50), D_55)=B_50 | ~r2_hidden(D_55, A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.34/6.57  tff(c_163, plain, (![A_89, D_90]: (r2_hidden(k1_funct_1(A_89, D_90), k2_relat_1(A_89)) | ~r2_hidden(D_90, k1_relat_1(A_89)) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_170, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, k1_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden(D_55, A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_163])).
% 15.34/6.57  tff(c_174, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_170])).
% 15.34/6.57  tff(c_7995, plain, (![B_2290, A_2291, C_2292, B_2293]: (r2_hidden(B_2290, k2_relat_1('#skF_6'(A_2291, B_2290))) | ~r2_hidden(C_2292, k2_relat_1('#skF_6'(A_2291, B_2293))))), inference(resolution, [status(thm)], [c_7571, c_174])).
% 15.34/6.57  tff(c_8091, plain, (![B_2290, A_49, C_2292]: (r2_hidden(B_2290, k2_relat_1('#skF_6'(A_49, B_2290))) | ~r2_hidden(C_2292, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_66, c_7995])).
% 15.34/6.57  tff(c_9534, plain, (![C_2696]: (~r2_hidden(C_2696, k2_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_8091])).
% 15.34/6.57  tff(c_9605, plain, (![B_2766]: (r1_tarski(k2_relat_1(k1_xboole_0), B_2766))), inference(resolution, [status(thm)], [c_6, c_9534])).
% 15.34/6.57  tff(c_175, plain, (![B_91, A_92, D_93]: (r2_hidden(B_91, k2_relat_1('#skF_6'(A_92, B_91))) | ~r2_hidden(D_93, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_170])).
% 15.34/6.57  tff(c_182, plain, (![B_94, A_95, B_96]: (r2_hidden(B_94, k2_relat_1('#skF_6'(A_95, B_94))) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_6, c_175])).
% 15.34/6.57  tff(c_194, plain, (![B_50, A_49, B_96]: (r2_hidden(B_50, k2_relat_1(k1_xboole_0)) | r1_tarski(A_49, B_96) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_66, c_182])).
% 15.34/6.57  tff(c_225, plain, (![A_99, B_100]: (r1_tarski(A_99, B_100) | k1_xboole_0!=A_99)), inference(splitLeft, [status(thm)], [c_194])).
% 15.34/6.57  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.34/6.57  tff(c_232, plain, (![B_100, A_99]: (B_100=A_99 | ~r1_tarski(B_100, A_99) | k1_xboole_0!=A_99)), inference(resolution, [status(thm)], [c_225, c_8])).
% 15.34/6.57  tff(c_9715, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_9605, c_232])).
% 15.34/6.57  tff(c_68, plain, (![A_66, B_67]: (k1_xboole_0!=A_66 | '#skF_6'(A_66, B_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_64])).
% 15.34/6.57  tff(c_78, plain, (![A_66]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_66)), inference(superposition, [status(thm), theory('equality')], [c_68, c_40])).
% 15.34/6.57  tff(c_98, plain, (![A_66]: (k1_xboole_0!=A_66)), inference(splitLeft, [status(thm)], [c_78])).
% 15.34/6.57  tff(c_104, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_98])).
% 15.34/6.57  tff(c_105, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_78])).
% 15.34/6.57  tff(c_116, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_68, c_38])).
% 15.34/6.57  tff(c_76, plain, (![A_66]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_66)), inference(superposition, [status(thm), theory('equality')], [c_68, c_42])).
% 15.34/6.57  tff(c_84, plain, (![A_66]: (k1_xboole_0!=A_66)), inference(splitLeft, [status(thm)], [c_76])).
% 15.34/6.57  tff(c_91, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_84])).
% 15.34/6.57  tff(c_92, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_76])).
% 15.34/6.57  tff(c_44, plain, (![C_57]: (~r1_tarski(k2_relat_1(C_57), '#skF_7') | k1_relat_1(C_57)!='#skF_8' | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.34/6.57  tff(c_253, plain, (![C_105]: (k1_relat_1(C_105)!='#skF_8' | ~v1_funct_1(C_105) | ~v1_relat_1(C_105) | k2_relat_1(C_105)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_225, c_44])).
% 15.34/6.57  tff(c_256, plain, (k1_relat_1(k1_xboole_0)!='#skF_8' | ~v1_funct_1(k1_xboole_0) | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_253])).
% 15.34/6.57  tff(c_262, plain, (k1_xboole_0!='#skF_8' | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_116, c_256])).
% 15.34/6.57  tff(c_266, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_262])).
% 15.34/6.57  tff(c_9721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9715, c_266])).
% 15.34/6.57  tff(c_9724, plain, (![B_2801, A_2802]: (r2_hidden(B_2801, k2_relat_1('#skF_6'(A_2802, B_2801))) | k1_xboole_0!=A_2802)), inference(splitRight, [status(thm)], [c_8091])).
% 15.34/6.57  tff(c_9941, plain, (![B_50, A_49]: (r2_hidden(B_50, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49 | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_66, c_9724])).
% 15.34/6.57  tff(c_10249, plain, (![A_49]: (k1_xboole_0!=A_49 | k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_9941])).
% 15.34/6.57  tff(c_10255, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_10249])).
% 15.34/6.57  tff(c_10256, plain, (![B_50]: (r2_hidden(B_50, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_9941])).
% 15.34/6.57  tff(c_281, plain, (![A_49, B_50, C_107]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_107), A_49) | ~r2_hidden(C_107, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_276])).
% 15.34/6.57  tff(c_200, plain, (![A_97, C_98]: (k1_funct_1(A_97, '#skF_5'(A_97, k2_relat_1(A_97), C_98))=C_98 | ~r2_hidden(C_98, k2_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_210, plain, (![C_98, B_50, A_49]: (C_98=B_50 | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_98), A_49) | ~r2_hidden(C_98, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_36])).
% 15.34/6.57  tff(c_9947, plain, (![C_2837, B_2838, A_2839]: (C_2837=B_2838 | ~r2_hidden('#skF_5'('#skF_6'(A_2839, B_2838), k2_relat_1('#skF_6'(A_2839, B_2838)), C_2837), A_2839) | ~r2_hidden(C_2837, k2_relat_1('#skF_6'(A_2839, B_2838))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_210])).
% 15.34/6.57  tff(c_9982, plain, (![C_2874, B_2875, A_2876]: (C_2874=B_2875 | ~r2_hidden(C_2874, k2_relat_1('#skF_6'(A_2876, B_2875))))), inference(resolution, [status(thm)], [c_281, c_9947])).
% 15.34/6.57  tff(c_10061, plain, (![C_2874, B_50, A_49]: (C_2874=B_50 | ~r2_hidden(C_2874, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_66, c_9982])).
% 15.34/6.57  tff(c_10095, plain, (![A_49]: (k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_10061])).
% 15.34/6.57  tff(c_10111, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_10095])).
% 15.34/6.57  tff(c_10112, plain, (![C_2874, B_50]: (C_2874=B_50 | ~r2_hidden(C_2874, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_10061])).
% 15.34/6.57  tff(c_10872, plain, (![C_3093, B_3094]: (C_3093=B_3094)), inference(demodulation, [status(thm), theory('equality')], [c_10256, c_10112])).
% 15.34/6.57  tff(c_14718, plain, (![B_3094]: (B_3094!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10872, c_49])).
% 15.34/6.57  tff(c_15100, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_14718])).
% 15.34/6.57  tff(c_15102, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_262])).
% 15.34/6.57  tff(c_67, plain, (![B_50]: ('#skF_6'(k1_xboole_0, B_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_64])).
% 15.34/6.57  tff(c_18, plain, (![A_9, D_48]: (r2_hidden(k1_funct_1(A_9, D_48), k2_relat_1(A_9)) | ~r2_hidden(D_48, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_15113, plain, (![D_48]: (r2_hidden(k1_funct_1(k1_xboole_0, D_48), k1_xboole_0) | ~r2_hidden(D_48, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15102, c_18])).
% 15.34/6.57  tff(c_15133, plain, (![D_4699]: (r2_hidden(k1_funct_1(k1_xboole_0, D_4699), k1_xboole_0) | ~r2_hidden(D_4699, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_105, c_116, c_15113])).
% 15.34/6.57  tff(c_15135, plain, (![B_50, D_4699]: (r2_hidden(B_50, k2_relat_1('#skF_6'(k1_xboole_0, B_50))) | ~r2_hidden(D_4699, k1_xboole_0))), inference(resolution, [status(thm)], [c_15133, c_174])).
% 15.34/6.57  tff(c_15145, plain, (![B_50, D_4699]: (r2_hidden(B_50, k1_xboole_0) | ~r2_hidden(D_4699, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_15102, c_67, c_15135])).
% 15.34/6.57  tff(c_15152, plain, (![D_4699]: (~r2_hidden(D_4699, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_15145])).
% 15.34/6.57  tff(c_15161, plain, (![A_4701, C_4702]: (r2_hidden('#skF_5'(A_4701, k2_relat_1(A_4701), C_4702), k1_relat_1(A_4701)) | ~r2_hidden(C_4702, k2_relat_1(A_4701)) | ~v1_funct_1(A_4701) | ~v1_relat_1(A_4701))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_23336, plain, (![B_7089, A_7090, C_7091]: (r2_hidden(B_7089, k2_relat_1('#skF_6'(k1_relat_1(A_7090), B_7089))) | ~r2_hidden(C_7091, k2_relat_1(A_7090)) | ~v1_funct_1(A_7090) | ~v1_relat_1(A_7090))), inference(resolution, [status(thm)], [c_15161, c_174])).
% 15.34/6.57  tff(c_24542, plain, (![B_7492, A_7493, B_7494]: (r2_hidden(B_7492, k2_relat_1('#skF_6'(k1_relat_1(A_7493), B_7492))) | ~v1_funct_1(A_7493) | ~v1_relat_1(A_7493) | r1_tarski(k2_relat_1(A_7493), B_7494))), inference(resolution, [status(thm)], [c_6, c_23336])).
% 15.34/6.57  tff(c_25007, plain, (![B_7492, A_49, B_50, B_7494]: (r2_hidden(B_7492, k2_relat_1('#skF_6'(A_49, B_7492))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | r1_tarski(k2_relat_1('#skF_6'(A_49, B_50)), B_7494))), inference(superposition, [status(thm), theory('equality')], [c_38, c_24542])).
% 15.34/6.57  tff(c_25211, plain, (![B_7565, A_7566, B_7567, B_7568]: (r2_hidden(B_7565, k2_relat_1('#skF_6'(A_7566, B_7565))) | r1_tarski(k2_relat_1('#skF_6'(A_7566, B_7567)), B_7568))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_25007])).
% 15.34/6.57  tff(c_25671, plain, (![B_50, A_49, B_7567, B_7568]: (r2_hidden(B_50, k2_relat_1(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_6'(A_49, B_7567)), B_7568) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_66, c_25211])).
% 15.34/6.57  tff(c_25699, plain, (![B_50, A_49, B_7567, B_7568]: (r2_hidden(B_50, k1_xboole_0) | r1_tarski(k2_relat_1('#skF_6'(A_49, B_7567)), B_7568) | k1_xboole_0!=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_15102, c_25671])).
% 15.34/6.57  tff(c_26073, plain, (![A_7676, B_7677, B_7678]: (r1_tarski(k2_relat_1('#skF_6'(A_7676, B_7677)), B_7678) | k1_xboole_0!=A_7676)), inference(negUnitSimplification, [status(thm)], [c_15152, c_25699])).
% 15.34/6.57  tff(c_26332, plain, (![A_7676, B_7677, B_7678]: (k2_relat_1('#skF_6'(A_7676, B_7677))=B_7678 | k1_xboole_0!=B_7678 | k1_xboole_0!=A_7676)), inference(resolution, [status(thm)], [c_26073, c_232])).
% 15.34/6.57  tff(c_26393, plain, (![B_7677]: (k2_relat_1('#skF_6'(k1_xboole_0, B_7677))=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_26332])).
% 15.34/6.57  tff(c_15292, plain, (![A_4726, B_4727]: (r2_hidden('#skF_3'(A_4726, B_4727), k1_relat_1(A_4726)) | r2_hidden('#skF_4'(A_4726, B_4727), B_4727) | k2_relat_1(A_4726)=B_4727 | ~v1_funct_1(A_4726) | ~v1_relat_1(A_4726))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_15309, plain, (![A_49, B_50, B_4727]: (r2_hidden('#skF_3'('#skF_6'(A_49, B_50), B_4727), A_49) | r2_hidden('#skF_4'('#skF_6'(A_49, B_50), B_4727), B_4727) | k2_relat_1('#skF_6'(A_49, B_50))=B_4727 | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_15292])).
% 15.34/6.57  tff(c_30296, plain, (![A_8710, B_8711, B_8712]: (r2_hidden('#skF_3'('#skF_6'(A_8710, B_8711), B_8712), A_8710) | r2_hidden('#skF_4'('#skF_6'(A_8710, B_8711), B_8712), B_8712) | k2_relat_1('#skF_6'(A_8710, B_8711))=B_8712)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_15309])).
% 15.34/6.57  tff(c_30338, plain, (![B_8711, B_8712]: (r2_hidden('#skF_4'('#skF_6'(k1_xboole_0, B_8711), B_8712), B_8712) | k2_relat_1('#skF_6'(k1_xboole_0, B_8711))=B_8712)), inference(resolution, [status(thm)], [c_30296, c_15152])).
% 15.34/6.57  tff(c_30861, plain, (![B_8712]: (r2_hidden('#skF_4'(k1_xboole_0, B_8712), B_8712) | k1_xboole_0=B_8712)), inference(demodulation, [status(thm), theory('equality')], [c_26393, c_67, c_30338])).
% 15.34/6.57  tff(c_15173, plain, (![A_49, B_50, C_4702]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_4702), A_49) | ~r2_hidden(C_4702, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_15161])).
% 15.34/6.57  tff(c_15181, plain, (![A_49, B_50, C_4702]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_4702), A_49) | ~r2_hidden(C_4702, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_15173])).
% 15.34/6.57  tff(c_28625, plain, (![C_8377, B_8378, A_8379]: (C_8377=B_8378 | ~r2_hidden('#skF_5'('#skF_6'(A_8379, B_8378), k2_relat_1('#skF_6'(A_8379, B_8378)), C_8377), A_8379) | ~r2_hidden(C_8377, k2_relat_1('#skF_6'(A_8379, B_8378))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_210])).
% 15.34/6.57  tff(c_28664, plain, (![C_8414, B_8415, A_8416]: (C_8414=B_8415 | ~r2_hidden(C_8414, k2_relat_1('#skF_6'(A_8416, B_8415))))), inference(resolution, [status(thm)], [c_15181, c_28625])).
% 15.34/6.57  tff(c_53282, plain, (![A_11759, B_11760, B_11761]: ('#skF_1'(k2_relat_1('#skF_6'(A_11759, B_11760)), B_11761)=B_11760 | r1_tarski(k2_relat_1('#skF_6'(A_11759, B_11760)), B_11761))), inference(resolution, [status(thm)], [c_6, c_28664])).
% 15.34/6.57  tff(c_53425, plain, (![A_11759, B_11760]: (k1_relat_1('#skF_6'(A_11759, B_11760))!='#skF_8' | ~v1_funct_1('#skF_6'(A_11759, B_11760)) | ~v1_relat_1('#skF_6'(A_11759, B_11760)) | '#skF_1'(k2_relat_1('#skF_6'(A_11759, B_11760)), '#skF_7')=B_11760)), inference(resolution, [status(thm)], [c_53282, c_44])).
% 15.34/6.57  tff(c_53813, plain, (![A_11796, B_11797]: (A_11796!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(A_11796, B_11797)), '#skF_7')=B_11797)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_53425])).
% 15.34/6.57  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.34/6.57  tff(c_54615, plain, (![B_11868, A_11869]: (~r2_hidden(B_11868, '#skF_7') | r1_tarski(k2_relat_1('#skF_6'(A_11869, B_11868)), '#skF_7') | A_11869!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_53813, c_4])).
% 15.34/6.57  tff(c_54656, plain, (![A_11869, B_11868]: (k1_relat_1('#skF_6'(A_11869, B_11868))!='#skF_8' | ~v1_funct_1('#skF_6'(A_11869, B_11868)) | ~v1_relat_1('#skF_6'(A_11869, B_11868)) | ~r2_hidden(B_11868, '#skF_7') | A_11869!='#skF_8')), inference(resolution, [status(thm)], [c_54615, c_44])).
% 15.34/6.57  tff(c_54948, plain, (![B_11868, A_11869]: (~r2_hidden(B_11868, '#skF_7') | A_11869!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54656])).
% 15.34/6.57  tff(c_54962, plain, (![A_11869]: (A_11869!='#skF_8')), inference(splitLeft, [status(thm)], [c_54948])).
% 15.34/6.57  tff(c_54966, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_54962])).
% 15.34/6.57  tff(c_54968, plain, (![B_11904]: (~r2_hidden(B_11904, '#skF_7'))), inference(splitRight, [status(thm)], [c_54948])).
% 15.34/6.57  tff(c_54992, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_30861, c_54968])).
% 15.34/6.57  tff(c_55030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_54992])).
% 15.34/6.57  tff(c_55034, plain, (![B_11939]: (r2_hidden(B_11939, k1_xboole_0))), inference(splitRight, [status(thm)], [c_15145])).
% 15.34/6.57  tff(c_55072, plain, (![A_11942]: (r1_tarski(A_11942, k1_xboole_0))), inference(resolution, [status(thm)], [c_55034, c_4])).
% 15.34/6.57  tff(c_55082, plain, (![A_11943]: (k1_xboole_0=A_11943)), inference(resolution, [status(thm)], [c_55072, c_232])).
% 15.34/6.57  tff(c_55127, plain, (![A_11943]: (A_11943!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_55082, c_49])).
% 15.34/6.57  tff(c_55145, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_55127])).
% 15.34/6.57  tff(c_55146, plain, (![B_50]: (r2_hidden(B_50, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_194])).
% 15.34/6.57  tff(c_55261, plain, (![A_12311, C_12312]: (r2_hidden('#skF_5'(A_12311, k2_relat_1(A_12311), C_12312), k1_relat_1(A_12311)) | ~r2_hidden(C_12312, k2_relat_1(A_12311)) | ~v1_funct_1(A_12311) | ~v1_relat_1(A_12311))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_55270, plain, (![A_49, B_50, C_12312]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_12312), A_49) | ~r2_hidden(C_12312, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_55261])).
% 15.34/6.57  tff(c_55275, plain, (![A_49, B_50, C_12312]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_12312), A_49) | ~r2_hidden(C_12312, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_55270])).
% 15.34/6.57  tff(c_55182, plain, (![A_12304, C_12305]: (k1_funct_1(A_12304, '#skF_5'(A_12304, k2_relat_1(A_12304), C_12305))=C_12305 | ~r2_hidden(C_12305, k2_relat_1(A_12304)) | ~v1_funct_1(A_12304) | ~v1_relat_1(A_12304))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_55192, plain, (![C_12305, B_50, A_49]: (C_12305=B_50 | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_12305), A_49) | ~r2_hidden(C_12305, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_55182, c_36])).
% 15.34/6.57  tff(c_56649, plain, (![C_13296, B_13297, A_13298]: (C_13296=B_13297 | ~r2_hidden('#skF_5'('#skF_6'(A_13298, B_13297), k2_relat_1('#skF_6'(A_13298, B_13297)), C_13296), A_13298) | ~r2_hidden(C_13296, k2_relat_1('#skF_6'(A_13298, B_13297))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_55192])).
% 15.34/6.57  tff(c_56665, plain, (![C_13299, B_13300, A_13301]: (C_13299=B_13300 | ~r2_hidden(C_13299, k2_relat_1('#skF_6'(A_13301, B_13300))))), inference(resolution, [status(thm)], [c_55275, c_56649])).
% 15.34/6.57  tff(c_56729, plain, (![C_13299, B_50, A_49]: (C_13299=B_50 | ~r2_hidden(C_13299, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_66, c_56665])).
% 15.34/6.57  tff(c_56762, plain, (![C_13299, B_50, A_49]: (C_13299=B_50 | k1_xboole_0!=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_55146, c_56729])).
% 15.34/6.57  tff(c_56763, plain, (![A_49]: (k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_56762])).
% 15.34/6.57  tff(c_56776, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_56763])).
% 15.34/6.57  tff(c_56813, plain, (![C_13305, B_13306]: (C_13305=B_13306)), inference(splitRight, [status(thm)], [c_56762])).
% 15.34/6.57  tff(c_61741, plain, (![B_13306]: (B_13306!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_56813, c_49])).
% 15.34/6.57  tff(c_62099, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_61741])).
% 15.34/6.57  tff(c_62100, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_46])).
% 15.34/6.57  tff(c_16, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.34/6.57  tff(c_62125, plain, (![A_15051]: (k1_relat_1(A_15051)!='#skF_8' | A_15051='#skF_8' | ~v1_relat_1(A_15051))), inference(demodulation, [status(thm), theory('equality')], [c_62100, c_62100, c_16])).
% 15.34/6.57  tff(c_62128, plain, (![A_49, B_50]: (k1_relat_1('#skF_6'(A_49, B_50))!='#skF_8' | '#skF_6'(A_49, B_50)='#skF_8')), inference(resolution, [status(thm)], [c_42, c_62125])).
% 15.34/6.57  tff(c_62138, plain, (![A_15053, B_15054]: (A_15053!='#skF_8' | '#skF_6'(A_15053, B_15054)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_62128])).
% 15.34/6.57  tff(c_62148, plain, (![A_15053]: (v1_relat_1('#skF_8') | A_15053!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62138, c_42])).
% 15.34/6.57  tff(c_62163, plain, (![A_15053]: (A_15053!='#skF_8')), inference(splitLeft, [status(thm)], [c_62148])).
% 15.34/6.57  tff(c_62101, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_46])).
% 15.34/6.57  tff(c_62107, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62100, c_62101])).
% 15.34/6.57  tff(c_62169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62163, c_62107])).
% 15.34/6.57  tff(c_62170, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_62148])).
% 15.34/6.57  tff(c_62146, plain, (![A_15053]: (v1_funct_1('#skF_8') | A_15053!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62138, c_40])).
% 15.34/6.57  tff(c_62154, plain, (![A_15053]: (A_15053!='#skF_8')), inference(splitLeft, [status(thm)], [c_62146])).
% 15.34/6.57  tff(c_62160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62154, c_62107])).
% 15.34/6.57  tff(c_62161, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_62146])).
% 15.34/6.57  tff(c_62181, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_62138, c_38])).
% 15.34/6.57  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.34/6.57  tff(c_62130, plain, (![A_49, B_50]: (A_49!='#skF_8' | '#skF_6'(A_49, B_50)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_62128])).
% 15.34/6.57  tff(c_62675, plain, (![A_15558, C_15559]: (r2_hidden('#skF_5'(A_15558, k2_relat_1(A_15558), C_15559), k1_relat_1(A_15558)) | ~r2_hidden(C_15559, k2_relat_1(A_15558)) | ~v1_funct_1(A_15558) | ~v1_relat_1(A_15558))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_62684, plain, (![A_49, B_50, C_15559]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_15559), A_49) | ~r2_hidden(C_15559, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_62675])).
% 15.34/6.57  tff(c_63020, plain, (![A_15645, B_15646, C_15647]: (r2_hidden('#skF_5'('#skF_6'(A_15645, B_15646), k2_relat_1('#skF_6'(A_15645, B_15646)), C_15647), A_15645) | ~r2_hidden(C_15647, k2_relat_1('#skF_6'(A_15645, B_15646))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_62684])).
% 15.34/6.57  tff(c_62493, plain, (![A_15490, D_15491]: (r2_hidden(k1_funct_1(A_15490, D_15491), k2_relat_1(A_15490)) | ~r2_hidden(D_15491, k1_relat_1(A_15490)) | ~v1_funct_1(A_15490) | ~v1_relat_1(A_15490))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_62564, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, k1_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden(D_55, A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_62493])).
% 15.34/6.57  tff(c_62592, plain, (![B_50, A_49, D_55]: (r2_hidden(B_50, k2_relat_1('#skF_6'(A_49, B_50))) | ~r2_hidden(D_55, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_62564])).
% 15.34/6.57  tff(c_63036, plain, (![B_15648, A_15649, C_15650, B_15651]: (r2_hidden(B_15648, k2_relat_1('#skF_6'(A_15649, B_15648))) | ~r2_hidden(C_15650, k2_relat_1('#skF_6'(A_15649, B_15651))))), inference(resolution, [status(thm)], [c_63020, c_62592])).
% 15.34/6.57  tff(c_63077, plain, (![B_15652, A_15653, B_15654, B_15655]: (r2_hidden(B_15652, k2_relat_1('#skF_6'(A_15653, B_15652))) | r1_tarski(k2_relat_1('#skF_6'(A_15653, B_15654)), B_15655))), inference(resolution, [status(thm)], [c_6, c_63036])).
% 15.34/6.57  tff(c_62108, plain, (![C_57]: (~r1_tarski(k2_relat_1(C_57), '#skF_8') | k1_relat_1(C_57)!='#skF_8' | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(demodulation, [status(thm), theory('equality')], [c_62107, c_44])).
% 15.34/6.57  tff(c_63111, plain, (![A_15653, B_15654, B_15652]: (k1_relat_1('#skF_6'(A_15653, B_15654))!='#skF_8' | ~v1_funct_1('#skF_6'(A_15653, B_15654)) | ~v1_relat_1('#skF_6'(A_15653, B_15654)) | r2_hidden(B_15652, k2_relat_1('#skF_6'(A_15653, B_15652))))), inference(resolution, [status(thm)], [c_63077, c_62108])).
% 15.34/6.57  tff(c_63136, plain, (![A_15656, B_15657]: (A_15656!='#skF_8' | r2_hidden(B_15657, k2_relat_1('#skF_6'(A_15656, B_15657))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_63111])).
% 15.34/6.57  tff(c_63147, plain, (![A_49, B_50]: (A_49!='#skF_8' | r2_hidden(B_50, k2_relat_1('#skF_8')) | A_49!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62130, c_63136])).
% 15.34/6.57  tff(c_63152, plain, (![A_49]: (A_49!='#skF_8' | A_49!='#skF_8')), inference(splitLeft, [status(thm)], [c_63147])).
% 15.34/6.57  tff(c_63158, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_63152])).
% 15.34/6.57  tff(c_63159, plain, (![B_50]: (r2_hidden(B_50, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_63147])).
% 15.34/6.57  tff(c_62689, plain, (![A_49, B_50, C_15559]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_15559), A_49) | ~r2_hidden(C_15559, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_62684])).
% 15.34/6.57  tff(c_62754, plain, (![A_15574, C_15575]: (k1_funct_1(A_15574, '#skF_5'(A_15574, k2_relat_1(A_15574), C_15575))=C_15575 | ~r2_hidden(C_15575, k2_relat_1(A_15574)) | ~v1_funct_1(A_15574) | ~v1_relat_1(A_15574))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_62764, plain, (![C_15575, B_50, A_49]: (C_15575=B_50 | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_15575), A_49) | ~r2_hidden(C_15575, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_62754, c_36])).
% 15.34/6.57  tff(c_63431, plain, (![C_15681, B_15682, A_15683]: (C_15681=B_15682 | ~r2_hidden('#skF_5'('#skF_6'(A_15683, B_15682), k2_relat_1('#skF_6'(A_15683, B_15682)), C_15681), A_15683) | ~r2_hidden(C_15681, k2_relat_1('#skF_6'(A_15683, B_15682))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_62764])).
% 15.34/6.57  tff(c_63447, plain, (![C_15684, B_15685, A_15686]: (C_15684=B_15685 | ~r2_hidden(C_15684, k2_relat_1('#skF_6'(A_15686, B_15685))))), inference(resolution, [status(thm)], [c_62689, c_63431])).
% 15.34/6.57  tff(c_63502, plain, (![C_15684, B_50, A_49]: (C_15684=B_50 | ~r2_hidden(C_15684, k2_relat_1('#skF_8')) | A_49!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62130, c_63447])).
% 15.34/6.57  tff(c_63529, plain, (![C_15684, B_50, A_49]: (C_15684=B_50 | A_49!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_63159, c_63502])).
% 15.34/6.57  tff(c_63530, plain, (![A_49]: (A_49!='#skF_8')), inference(splitLeft, [status(thm)], [c_63529])).
% 15.34/6.57  tff(c_63541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63530, c_62107])).
% 15.34/6.57  tff(c_63571, plain, (![C_15690, B_15691]: (C_15690=B_15691)), inference(splitRight, [status(thm)], [c_63529])).
% 15.34/6.57  tff(c_62593, plain, (![B_15509, A_15510, D_15511]: (r2_hidden(B_15509, k2_relat_1('#skF_6'(A_15510, B_15509))) | ~r2_hidden(D_15511, A_15510))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_62564])).
% 15.34/6.57  tff(c_62603, plain, (![B_15529, A_15530, B_15531]: (r2_hidden(B_15529, k2_relat_1('#skF_6'(A_15530, B_15529))) | r1_tarski(A_15530, B_15531))), inference(resolution, [status(thm)], [c_6, c_62593])).
% 15.34/6.57  tff(c_62619, plain, (![B_50, A_49, B_15531]: (r2_hidden(B_50, k2_relat_1('#skF_8')) | r1_tarski(A_49, B_15531) | A_49!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62130, c_62603])).
% 15.34/6.57  tff(c_62647, plain, (![A_15552, B_15553]: (r1_tarski(A_15552, B_15553) | A_15552!='#skF_8')), inference(splitLeft, [status(thm)], [c_62619])).
% 15.34/6.57  tff(c_62690, plain, (![C_15560]: (k1_relat_1(C_15560)!='#skF_8' | ~v1_funct_1(C_15560) | ~v1_relat_1(C_15560) | k2_relat_1(C_15560)!='#skF_8')), inference(resolution, [status(thm)], [c_62647, c_62108])).
% 15.34/6.57  tff(c_62693, plain, (k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | k2_relat_1('#skF_8')!='#skF_8'), inference(resolution, [status(thm)], [c_62170, c_62690])).
% 15.34/6.57  tff(c_62699, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62161, c_62181, c_62693])).
% 15.34/6.57  tff(c_66655, plain, (![C_15690]: (C_15690!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_63571, c_62699])).
% 15.34/6.57  tff(c_68024, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_66655])).
% 15.34/6.57  tff(c_68025, plain, (![B_50]: (r2_hidden(B_50, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_62619])).
% 15.34/6.57  tff(c_68064, plain, (![A_17242, C_17243]: (r2_hidden('#skF_5'(A_17242, k2_relat_1(A_17242), C_17243), k1_relat_1(A_17242)) | ~r2_hidden(C_17243, k2_relat_1(A_17242)) | ~v1_funct_1(A_17242) | ~v1_relat_1(A_17242))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_68079, plain, (![A_49, B_50, C_17243]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_17243), A_49) | ~r2_hidden(C_17243, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_68064])).
% 15.34/6.57  tff(c_68084, plain, (![A_49, B_50, C_17243]: (r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_17243), A_49) | ~r2_hidden(C_17243, k2_relat_1('#skF_6'(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_68079])).
% 15.34/6.57  tff(c_68208, plain, (![A_17390, C_17391]: (k1_funct_1(A_17390, '#skF_5'(A_17390, k2_relat_1(A_17390), C_17391))=C_17391 | ~r2_hidden(C_17391, k2_relat_1(A_17390)) | ~v1_funct_1(A_17390) | ~v1_relat_1(A_17390))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.34/6.57  tff(c_68243, plain, (![C_17391, B_50, A_49]: (C_17391=B_50 | ~r2_hidden(C_17391, k2_relat_1('#skF_6'(A_49, B_50))) | ~v1_funct_1('#skF_6'(A_49, B_50)) | ~v1_relat_1('#skF_6'(A_49, B_50)) | ~r2_hidden('#skF_5'('#skF_6'(A_49, B_50), k2_relat_1('#skF_6'(A_49, B_50)), C_17391), A_49))), inference(superposition, [status(thm), theory('equality')], [c_36, c_68208])).
% 15.34/6.57  tff(c_69803, plain, (![C_17723, B_17724, A_17725]: (C_17723=B_17724 | ~r2_hidden(C_17723, k2_relat_1('#skF_6'(A_17725, B_17724))) | ~r2_hidden('#skF_5'('#skF_6'(A_17725, B_17724), k2_relat_1('#skF_6'(A_17725, B_17724)), C_17723), A_17725))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_68243])).
% 15.34/6.57  tff(c_69819, plain, (![C_17726, B_17727, A_17728]: (C_17726=B_17727 | ~r2_hidden(C_17726, k2_relat_1('#skF_6'(A_17728, B_17727))))), inference(resolution, [status(thm)], [c_68084, c_69803])).
% 15.34/6.57  tff(c_69853, plain, (![C_17726, B_50, A_49]: (C_17726=B_50 | ~r2_hidden(C_17726, k2_relat_1('#skF_8')) | A_49!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62130, c_69819])).
% 15.34/6.57  tff(c_69866, plain, (![C_17726, B_50, A_49]: (C_17726=B_50 | A_49!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68025, c_69853])).
% 15.34/6.57  tff(c_69867, plain, (![A_49]: (A_49!='#skF_8')), inference(splitLeft, [status(thm)], [c_69866])).
% 15.34/6.57  tff(c_69874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69867, c_62107])).
% 15.34/6.57  tff(c_69907, plain, (![C_17732, B_17733]: (C_17732=B_17733)), inference(splitRight, [status(thm)], [c_69866])).
% 15.34/6.57  tff(c_68026, plain, (![B_17188]: (r2_hidden(B_17188, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_62619])).
% 15.34/6.57  tff(c_62202, plain, (![A_15063, B_15064, D_15065]: (k1_funct_1('#skF_6'(A_15063, B_15064), D_15065)=B_15064 | ~r2_hidden(D_15065, A_15063))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.34/6.57  tff(c_62211, plain, (![D_15065, B_50, A_49]: (k1_funct_1('#skF_8', D_15065)=B_50 | ~r2_hidden(D_15065, A_49) | A_49!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62130, c_62202])).
% 15.34/6.57  tff(c_68038, plain, (![B_17188, B_50]: (k1_funct_1('#skF_8', B_17188)=B_50 | k2_relat_1('#skF_8')!='#skF_8')), inference(resolution, [status(thm)], [c_68026, c_62211])).
% 15.34/6.57  tff(c_68085, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(splitLeft, [status(thm)], [c_68038])).
% 15.34/6.57  tff(c_70667, plain, (![B_17733]: (B_17733!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_69907, c_68085])).
% 15.34/6.57  tff(c_72190, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_70667])).
% 15.34/6.57  tff(c_72192, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_68038])).
% 15.34/6.57  tff(c_72206, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_72192, c_62108])).
% 15.34/6.57  tff(c_72215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62170, c_62161, c_62181, c_12, c_72206])).
% 15.34/6.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.34/6.57  
% 15.34/6.57  Inference rules
% 15.34/6.57  ----------------------
% 15.34/6.57  #Ref     : 39
% 15.34/6.57  #Sup     : 13780
% 15.34/6.57  #Fact    : 10
% 15.34/6.57  #Define  : 0
% 15.34/6.57  #Split   : 36
% 15.34/6.57  #Chain   : 0
% 15.34/6.57  #Close   : 0
% 15.34/6.57  
% 15.34/6.57  Ordering : KBO
% 15.34/6.57  
% 15.34/6.57  Simplification rules
% 15.34/6.57  ----------------------
% 15.34/6.57  #Subsume      : 4339
% 15.34/6.57  #Demod        : 3839
% 15.34/6.57  #Tautology    : 953
% 15.34/6.57  #SimpNegUnit  : 461
% 15.34/6.57  #BackRed      : 38
% 15.34/6.57  
% 15.34/6.57  #Partial instantiations: 12174
% 15.34/6.57  #Strategies tried      : 1
% 15.34/6.57  
% 15.34/6.57  Timing (in seconds)
% 15.34/6.57  ----------------------
% 15.34/6.58  Preprocessing        : 0.34
% 15.34/6.58  Parsing              : 0.17
% 15.34/6.58  CNF conversion       : 0.03
% 15.34/6.58  Main loop            : 5.41
% 15.34/6.58  Inferencing          : 1.40
% 15.34/6.58  Reduction            : 1.62
% 15.34/6.58  Demodulation         : 1.12
% 15.34/6.58  BG Simplification    : 0.19
% 15.34/6.58  Subsumption          : 1.83
% 15.34/6.58  Abstraction          : 0.21
% 15.34/6.58  MUC search           : 0.00
% 15.34/6.58  Cooper               : 0.00
% 15.34/6.58  Total                : 5.81
% 15.34/6.58  Index Insertion      : 0.00
% 15.34/6.58  Index Deletion       : 0.00
% 15.34/6.58  Index Matching       : 0.00
% 15.34/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
