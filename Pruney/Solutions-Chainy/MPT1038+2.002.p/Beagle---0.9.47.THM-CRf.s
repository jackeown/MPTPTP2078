%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:01 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 100 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 334 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
               => ( ( r1_partfun1(B,D)
                    & r1_partfun1(C,D) )
                 => r1_partfun1(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ( ( r1_partfun1(C,E)
                  & r1_partfun1(D,E)
                  & v1_partfun1(E,A) )
               => r1_partfun1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_partfun1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_32,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    r1_partfun1('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_235,plain,(
    ! [C_80,B_81,A_82] :
      ( v1_xboole_0(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(B_81,A_82)))
      | ~ v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_250,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_235])).

tff(c_253,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_254,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_partfun1(C_83,A_84)
      | ~ v1_funct_2(C_83,A_84,B_85)
      | ~ v1_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | v1_xboole_0(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_267,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_254])).

tff(c_277,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_267])).

tff(c_278,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_277])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_301,plain,(
    ! [C_92,E_90,D_89,B_93,A_91] :
      ( r1_partfun1(C_92,D_89)
      | ~ v1_partfun1(E_90,A_91)
      | ~ r1_partfun1(D_89,E_90)
      | ~ r1_partfun1(C_92,E_90)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1(E_90)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1(D_89)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_303,plain,(
    ! [C_92,A_91,B_93] :
      ( r1_partfun1(C_92,'#skF_4')
      | ~ v1_partfun1('#skF_5',A_91)
      | ~ r1_partfun1(C_92,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_93)))
      | ~ v1_funct_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_34,c_301])).

tff(c_330,plain,(
    ! [C_102,A_103,B_104] :
      ( r1_partfun1(C_102,'#skF_4')
      | ~ v1_partfun1('#skF_5',A_103)
      | ~ r1_partfun1(C_102,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(C_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_303])).

tff(c_335,plain,(
    ! [C_102] :
      ( r1_partfun1(C_102,'#skF_4')
      | ~ v1_partfun1('#skF_5','#skF_2')
      | ~ r1_partfun1(C_102,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_38,c_330])).

tff(c_342,plain,(
    ! [C_111] :
      ( r1_partfun1(C_111,'#skF_4')
      | ~ r1_partfun1(C_111,'#skF_5')
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_funct_1(C_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_278,c_335])).

tff(c_349,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ r1_partfun1('#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_342])).

tff(c_359,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_349])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_359])).

tff(c_363,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_251,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_235])).

tff(c_400,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_251])).

tff(c_252,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_235])).

tff(c_395,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_252])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_404,plain,(
    ! [A_115] :
      ( A_115 = '#skF_5'
      | ~ v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_395,c_6])).

tff(c_417,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_400,c_404])).

tff(c_431,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_36])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.29  
% 2.41/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.41/1.29  
% 2.41/1.29  %Foreground sorts:
% 2.41/1.29  
% 2.41/1.29  
% 2.41/1.29  %Background operators:
% 2.41/1.29  
% 2.41/1.29  
% 2.41/1.29  %Foreground operators:
% 2.41/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.41/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.41/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.41/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.29  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.41/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.29  
% 2.41/1.31  tff(f_132, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r1_partfun1(B, D) & r1_partfun1(C, D)) => r1_partfun1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_2)).
% 2.41/1.31  tff(f_73, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.41/1.31  tff(f_87, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.41/1.31  tff(f_109, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((r1_partfun1(C, E) & r1_partfun1(D, E)) & v1_partfun1(E, A)) => r1_partfun1(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_partfun1)).
% 2.41/1.31  tff(f_39, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.41/1.31  tff(c_32, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_36, plain, (r1_partfun1('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_235, plain, (![C_80, B_81, A_82]: (v1_xboole_0(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(B_81, A_82))) | ~v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.41/1.31  tff(c_250, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_235])).
% 2.41/1.31  tff(c_253, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_250])).
% 2.41/1.31  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_254, plain, (![C_83, A_84, B_85]: (v1_partfun1(C_83, A_84) | ~v1_funct_2(C_83, A_84, B_85) | ~v1_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | v1_xboole_0(B_85))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.41/1.31  tff(c_267, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_254])).
% 2.41/1.31  tff(c_277, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_267])).
% 2.41/1.31  tff(c_278, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_253, c_277])).
% 2.41/1.31  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_34, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.41/1.31  tff(c_301, plain, (![C_92, E_90, D_89, B_93, A_91]: (r1_partfun1(C_92, D_89) | ~v1_partfun1(E_90, A_91) | ~r1_partfun1(D_89, E_90) | ~r1_partfun1(C_92, E_90) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1(E_90) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1(D_89) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.41/1.31  tff(c_303, plain, (![C_92, A_91, B_93]: (r1_partfun1(C_92, '#skF_4') | ~v1_partfun1('#skF_5', A_91) | ~r1_partfun1(C_92, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_93))) | ~v1_funct_1(C_92))), inference(resolution, [status(thm)], [c_34, c_301])).
% 2.41/1.31  tff(c_330, plain, (![C_102, A_103, B_104]: (r1_partfun1(C_102, '#skF_4') | ~v1_partfun1('#skF_5', A_103) | ~r1_partfun1(C_102, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(C_102))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_303])).
% 2.41/1.31  tff(c_335, plain, (![C_102]: (r1_partfun1(C_102, '#skF_4') | ~v1_partfun1('#skF_5', '#skF_2') | ~r1_partfun1(C_102, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1(C_102))), inference(resolution, [status(thm)], [c_38, c_330])).
% 2.41/1.31  tff(c_342, plain, (![C_111]: (r1_partfun1(C_111, '#skF_4') | ~r1_partfun1(C_111, '#skF_5') | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1(C_111))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_278, c_335])).
% 2.41/1.31  tff(c_349, plain, (r1_partfun1('#skF_3', '#skF_4') | ~r1_partfun1('#skF_3', '#skF_5') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_342])).
% 2.41/1.31  tff(c_359, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_349])).
% 2.41/1.31  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_359])).
% 2.41/1.31  tff(c_363, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_250])).
% 2.41/1.31  tff(c_251, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_235])).
% 2.41/1.31  tff(c_400, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_251])).
% 2.41/1.31  tff(c_252, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_235])).
% 2.41/1.31  tff(c_395, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_252])).
% 2.41/1.31  tff(c_6, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.31  tff(c_404, plain, (![A_115]: (A_115='#skF_5' | ~v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_395, c_6])).
% 2.41/1.31  tff(c_417, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_400, c_404])).
% 2.41/1.31  tff(c_431, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_36])).
% 2.41/1.31  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_431])).
% 2.41/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.31  
% 2.41/1.31  Inference rules
% 2.41/1.31  ----------------------
% 2.41/1.31  #Ref     : 0
% 2.41/1.31  #Sup     : 74
% 2.41/1.31  #Fact    : 0
% 2.41/1.31  #Define  : 0
% 2.41/1.31  #Split   : 5
% 2.41/1.31  #Chain   : 0
% 2.41/1.31  #Close   : 0
% 2.41/1.31  
% 2.41/1.31  Ordering : KBO
% 2.41/1.31  
% 2.41/1.31  Simplification rules
% 2.41/1.31  ----------------------
% 2.41/1.31  #Subsume      : 13
% 2.41/1.31  #Demod        : 50
% 2.41/1.31  #Tautology    : 23
% 2.41/1.31  #SimpNegUnit  : 5
% 2.41/1.31  #BackRed      : 11
% 2.41/1.31  
% 2.41/1.31  #Partial instantiations: 0
% 2.41/1.31  #Strategies tried      : 1
% 2.41/1.31  
% 2.41/1.31  Timing (in seconds)
% 2.41/1.31  ----------------------
% 2.67/1.31  Preprocessing        : 0.29
% 2.67/1.31  Parsing              : 0.16
% 2.67/1.31  CNF conversion       : 0.02
% 2.67/1.31  Main loop            : 0.28
% 2.67/1.31  Inferencing          : 0.11
% 2.67/1.31  Reduction            : 0.08
% 2.67/1.31  Demodulation         : 0.06
% 2.67/1.31  BG Simplification    : 0.02
% 2.67/1.31  Subsumption          : 0.05
% 2.67/1.31  Abstraction          : 0.01
% 2.67/1.31  MUC search           : 0.00
% 2.67/1.31  Cooper               : 0.00
% 2.67/1.31  Total                : 0.60
% 2.67/1.31  Index Insertion      : 0.00
% 2.67/1.31  Index Deletion       : 0.00
% 2.67/1.31  Index Matching       : 0.00
% 2.67/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
