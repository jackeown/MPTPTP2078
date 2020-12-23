%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 211 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 733 expanded)
%              Number of equality atoms :   13 ( 182 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_46,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_73,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_partfun1(C_57,A_58)
      | ~ v1_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_82,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_76])).

tff(c_87,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_90])).

tff(c_95,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_253,plain,(
    ! [F_109,A_110,B_111,C_112] :
      ( r2_hidden(F_109,k5_partfun1(A_110,B_111,C_112))
      | ~ r1_partfun1(C_112,F_109)
      | ~ v1_partfun1(F_109,A_110)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_257,plain,(
    ! [C_112] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_112))
      | ~ r1_partfun1(C_112,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_52,c_253])).

tff(c_267,plain,(
    ! [C_113] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_113))
      | ~ r1_partfun1(C_113,'#skF_8')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_95,c_257])).

tff(c_277,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_267])).

tff(c_284,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_277])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_284])).

tff(c_288,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_287,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_293,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_287])).

tff(c_305,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_46])).

tff(c_306,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_58])).

tff(c_307,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_52])).

tff(c_308,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_partfun1(C_115,A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_315,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_307,c_308])).

tff(c_317,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_298,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_54])).

tff(c_318,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_partfun1(C_118,A_119)
      | ~ v1_funct_2(C_118,A_119,B_120)
      | ~ v1_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | v1_xboole_0(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_321,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_307,c_318])).

tff(c_327,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_298,c_321])).

tff(c_328,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_327])).

tff(c_424,plain,(
    ! [F_161,A_162,B_163,C_164] :
      ( r2_hidden(F_161,k5_partfun1(A_162,B_163,C_164))
      | ~ r1_partfun1(C_164,F_161)
      | ~ v1_partfun1(F_161,A_162)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_426,plain,(
    ! [C_164] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_164))
      | ~ r1_partfun1(C_164,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_307,c_424])).

tff(c_435,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_165))
      | ~ r1_partfun1(C_165,'#skF_8')
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_328,c_426])).

tff(c_441,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_306,c_435])).

tff(c_447,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_441])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_447])).

tff(c_450,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_600,plain,(
    ! [F_214,A_215,B_216,C_217] :
      ( r2_hidden(F_214,k5_partfun1(A_215,B_216,C_217))
      | ~ r1_partfun1(C_217,F_214)
      | ~ v1_partfun1(F_214,A_215)
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_602,plain,(
    ! [C_217] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_217))
      | ~ r1_partfun1(C_217,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_217) ) ),
    inference(resolution,[status(thm)],[c_307,c_600])).

tff(c_611,plain,(
    ! [C_218] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_218))
      | ~ r1_partfun1(C_218,'#skF_8')
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_450,c_602])).

tff(c_617,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_306,c_611])).

tff(c_623,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_617])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.64  
% 3.19/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.65  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.19/1.65  
% 3.19/1.65  %Foreground sorts:
% 3.19/1.65  
% 3.19/1.65  
% 3.19/1.65  %Background operators:
% 3.19/1.65  
% 3.19/1.65  
% 3.19/1.65  %Foreground operators:
% 3.19/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.19/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.19/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.19/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.19/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.19/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.19/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.19/1.65  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 3.19/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.65  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.19/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.65  
% 3.19/1.66  tff(f_92, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 3.19/1.66  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.19/1.66  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.19/1.66  tff(f_71, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 3.19/1.66  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.19/1.66  tff(c_46, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_50, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_48, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_61, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 3.19/1.66  tff(c_54, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.66  tff(c_73, plain, (![C_57, A_58, B_59]: (v1_partfun1(C_57, A_58) | ~v1_funct_2(C_57, A_58, B_59) | ~v1_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.19/1.66  tff(c_76, plain, (v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_73])).
% 3.19/1.66  tff(c_82, plain, (v1_partfun1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_76])).
% 3.19/1.66  tff(c_87, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_82])).
% 3.19/1.66  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.66  tff(c_90, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_87, c_2])).
% 3.19/1.66  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_90])).
% 3.19/1.66  tff(c_95, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_82])).
% 3.19/1.66  tff(c_253, plain, (![F_109, A_110, B_111, C_112]: (r2_hidden(F_109, k5_partfun1(A_110, B_111, C_112)) | ~r1_partfun1(C_112, F_109) | ~v1_partfun1(F_109, A_110) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(F_109) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.66  tff(c_257, plain, (![C_112]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', C_112)) | ~r1_partfun1(C_112, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_112))), inference(resolution, [status(thm)], [c_52, c_253])).
% 3.19/1.66  tff(c_267, plain, (![C_113]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', C_113)) | ~r1_partfun1(C_113, '#skF_8') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_113))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_95, c_257])).
% 3.19/1.66  tff(c_277, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_267])).
% 3.19/1.66  tff(c_284, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_277])).
% 3.19/1.66  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_284])).
% 3.19/1.66  tff(c_288, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 3.19/1.66  tff(c_287, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 3.19/1.66  tff(c_293, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_287])).
% 3.19/1.66  tff(c_305, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_46])).
% 3.19/1.66  tff(c_306, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_58])).
% 3.19/1.66  tff(c_307, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_52])).
% 3.19/1.66  tff(c_308, plain, (![C_115, A_116, B_117]: (v1_partfun1(C_115, A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.19/1.66  tff(c_315, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_307, c_308])).
% 3.19/1.66  tff(c_317, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_315])).
% 3.19/1.66  tff(c_298, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_54])).
% 3.19/1.66  tff(c_318, plain, (![C_118, A_119, B_120]: (v1_partfun1(C_118, A_119) | ~v1_funct_2(C_118, A_119, B_120) | ~v1_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | v1_xboole_0(B_120))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.19/1.66  tff(c_321, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_307, c_318])).
% 3.19/1.66  tff(c_327, plain, (v1_partfun1('#skF_8', '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_298, c_321])).
% 3.19/1.66  tff(c_328, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_317, c_327])).
% 3.19/1.66  tff(c_424, plain, (![F_161, A_162, B_163, C_164]: (r2_hidden(F_161, k5_partfun1(A_162, B_163, C_164)) | ~r1_partfun1(C_164, F_161) | ~v1_partfun1(F_161, A_162) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(F_161) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.66  tff(c_426, plain, (![C_164]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_164)) | ~r1_partfun1(C_164, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_164))), inference(resolution, [status(thm)], [c_307, c_424])).
% 3.19/1.66  tff(c_435, plain, (![C_165]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_165)) | ~r1_partfun1(C_165, '#skF_8') | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_165))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_328, c_426])).
% 3.19/1.66  tff(c_441, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_306, c_435])).
% 3.19/1.66  tff(c_447, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_441])).
% 3.19/1.66  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_447])).
% 3.19/1.66  tff(c_450, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_315])).
% 3.19/1.66  tff(c_600, plain, (![F_214, A_215, B_216, C_217]: (r2_hidden(F_214, k5_partfun1(A_215, B_216, C_217)) | ~r1_partfun1(C_217, F_214) | ~v1_partfun1(F_214, A_215) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(F_214) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.19/1.66  tff(c_602, plain, (![C_217]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_217)) | ~r1_partfun1(C_217, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_217))), inference(resolution, [status(thm)], [c_307, c_600])).
% 3.19/1.66  tff(c_611, plain, (![C_218]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_218)) | ~r1_partfun1(C_218, '#skF_8') | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_218))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_450, c_602])).
% 3.19/1.66  tff(c_617, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_306, c_611])).
% 3.19/1.66  tff(c_623, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_617])).
% 3.19/1.66  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_623])).
% 3.19/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.66  
% 3.19/1.66  Inference rules
% 3.19/1.66  ----------------------
% 3.19/1.66  #Ref     : 0
% 3.19/1.66  #Sup     : 104
% 3.19/1.66  #Fact    : 0
% 3.19/1.66  #Define  : 0
% 3.19/1.66  #Split   : 6
% 3.19/1.66  #Chain   : 0
% 3.19/1.66  #Close   : 0
% 3.19/1.66  
% 3.19/1.66  Ordering : KBO
% 3.19/1.66  
% 3.19/1.66  Simplification rules
% 3.19/1.66  ----------------------
% 3.19/1.66  #Subsume      : 4
% 3.19/1.66  #Demod        : 77
% 3.19/1.66  #Tautology    : 16
% 3.19/1.66  #SimpNegUnit  : 7
% 3.19/1.66  #BackRed      : 2
% 3.19/1.66  
% 3.19/1.66  #Partial instantiations: 0
% 3.19/1.66  #Strategies tried      : 1
% 3.19/1.66  
% 3.19/1.66  Timing (in seconds)
% 3.19/1.66  ----------------------
% 3.19/1.66  Preprocessing        : 0.43
% 3.19/1.66  Parsing              : 0.16
% 3.19/1.66  CNF conversion       : 0.05
% 3.19/1.66  Main loop            : 0.41
% 3.19/1.66  Inferencing          : 0.16
% 3.19/1.66  Reduction            : 0.13
% 3.19/1.66  Demodulation         : 0.09
% 3.19/1.66  BG Simplification    : 0.04
% 3.19/1.66  Subsumption          : 0.07
% 3.19/1.66  Abstraction          : 0.03
% 3.19/1.66  MUC search           : 0.00
% 3.19/1.66  Cooper               : 0.00
% 3.19/1.66  Total                : 0.88
% 3.19/1.66  Index Insertion      : 0.00
% 3.19/1.66  Index Deletion       : 0.00
% 3.19/1.66  Index Matching       : 0.00
% 3.19/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
