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
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 211 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 667 expanded)
%              Number of equality atoms :   14 (  95 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_225,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( r2_relset_1(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_239,plain,(
    ! [C_84] :
      ( r2_relset_1('#skF_2','#skF_3',C_84,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_225])).

tff(c_245,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_239])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_209,plain,(
    ! [C_74,B_75,A_76] :
      ( ~ v1_xboole_0(C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_216,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_224,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_216])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_246,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_partfun1(C_85,A_86)
      | ~ v1_funct_2(C_85,A_86,B_87)
      | ~ v1_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | v1_xboole_0(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_258,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_246])).

tff(c_266,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_258])).

tff(c_267,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_266])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_255,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_246])).

tff(c_262,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_255])).

tff(c_263,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_262])).

tff(c_32,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_268,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r1_partfun1(C_89,D_88)
      | ~ v1_partfun1(D_88,A_90)
      | ~ v1_partfun1(C_89,A_90)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(D_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_270,plain,(
    ! [A_90,B_91] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_90)
      | ~ v1_partfun1('#skF_4',A_90)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_268])).

tff(c_273,plain,(
    ! [A_90,B_91] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_90)
      | ~ v1_partfun1('#skF_4',A_90)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_270])).

tff(c_290,plain,(
    ! [A_100,B_101] :
      ( ~ v1_partfun1('#skF_5',A_100)
      | ~ v1_partfun1('#skF_4',A_100)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_299,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_34,c_290])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_267,c_263,c_299])).

tff(c_305,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_309,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_28])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_309])).

tff(c_321,plain,(
    ! [A_102] : ~ r2_hidden(A_102,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_326,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_320,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_215,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_331,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_331])).

tff(c_343,plain,(
    ! [A_104] : ~ r2_hidden(A_104,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_349,plain,(
    ! [B_105] : r1_tarski('#skF_4',B_105) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_391,plain,(
    ! [B_109] :
      ( B_109 = '#skF_4'
      | ~ r1_tarski(B_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_349,c_10])).

tff(c_406,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_326,c_391])).

tff(c_412,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_28])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_359,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_320,c_8])).

tff(c_367,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_40])).

tff(c_484,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( r2_relset_1(A_119,B_120,C_121,C_121)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_486,plain,(
    ! [C_121,D_122] :
      ( r2_relset_1('#skF_2','#skF_3',C_121,C_121)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_484])).

tff(c_491,plain,(
    ! [C_121,D_122] :
      ( r2_relset_1('#skF_2','#skF_3',C_121,C_121)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_486])).

tff(c_493,plain,(
    ! [D_122] : ~ m1_subset_1(D_122,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_367])).

tff(c_497,plain,(
    ! [C_123] :
      ( r2_relset_1('#skF_2','#skF_3',C_123,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_499,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_367,c_497])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.41  
% 2.38/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.41  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.38/1.41  
% 2.38/1.41  %Foreground sorts:
% 2.38/1.41  
% 2.38/1.41  
% 2.38/1.41  %Background operators:
% 2.38/1.41  
% 2.38/1.41  
% 2.38/1.41  %Foreground operators:
% 2.38/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.38/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.41  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.38/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.41  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.38/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.41  
% 2.53/1.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.53/1.43  tff(f_113, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.53/1.43  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.53/1.43  tff(f_46, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.53/1.43  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.53/1.43  tff(f_73, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.53/1.43  tff(f_90, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.53/1.43  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.43  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.43  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_225, plain, (![A_80, B_81, C_82, D_83]: (r2_relset_1(A_80, B_81, C_82, C_82) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.43  tff(c_239, plain, (![C_84]: (r2_relset_1('#skF_2', '#skF_3', C_84, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_40, c_225])).
% 2.53/1.43  tff(c_245, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_239])).
% 2.53/1.43  tff(c_16, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.43  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_209, plain, (![C_74, B_75, A_76]: (~v1_xboole_0(C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.43  tff(c_214, plain, (![A_76]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_209])).
% 2.53/1.43  tff(c_216, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_214])).
% 2.53/1.43  tff(c_224, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_16, c_216])).
% 2.53/1.43  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_246, plain, (![C_85, A_86, B_87]: (v1_partfun1(C_85, A_86) | ~v1_funct_2(C_85, A_86, B_87) | ~v1_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | v1_xboole_0(B_87))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.43  tff(c_258, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_246])).
% 2.53/1.43  tff(c_266, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_258])).
% 2.53/1.43  tff(c_267, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_224, c_266])).
% 2.53/1.43  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_255, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_246])).
% 2.53/1.43  tff(c_262, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_255])).
% 2.53/1.43  tff(c_263, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_224, c_262])).
% 2.53/1.43  tff(c_32, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_268, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r1_partfun1(C_89, D_88) | ~v1_partfun1(D_88, A_90) | ~v1_partfun1(C_89, A_90) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(D_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.53/1.43  tff(c_270, plain, (![A_90, B_91]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_90) | ~v1_partfun1('#skF_4', A_90) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_268])).
% 2.53/1.43  tff(c_273, plain, (![A_90, B_91]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_90) | ~v1_partfun1('#skF_4', A_90) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_270])).
% 2.53/1.43  tff(c_290, plain, (![A_100, B_101]: (~v1_partfun1('#skF_5', A_100) | ~v1_partfun1('#skF_4', A_100) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(splitLeft, [status(thm)], [c_273])).
% 2.53/1.43  tff(c_299, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_34, c_290])).
% 2.53/1.43  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_267, c_263, c_299])).
% 2.53/1.43  tff(c_305, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_273])).
% 2.53/1.43  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.43  tff(c_309, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_28])).
% 2.53/1.43  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_309])).
% 2.53/1.43  tff(c_321, plain, (![A_102]: (~r2_hidden(A_102, '#skF_5'))), inference(splitRight, [status(thm)], [c_214])).
% 2.53/1.43  tff(c_326, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_321])).
% 2.53/1.43  tff(c_320, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_214])).
% 2.53/1.43  tff(c_215, plain, (![A_76]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_209])).
% 2.53/1.43  tff(c_331, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_215])).
% 2.53/1.43  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_331])).
% 2.53/1.43  tff(c_343, plain, (![A_104]: (~r2_hidden(A_104, '#skF_4'))), inference(splitRight, [status(thm)], [c_215])).
% 2.53/1.43  tff(c_349, plain, (![B_105]: (r1_tarski('#skF_4', B_105))), inference(resolution, [status(thm)], [c_6, c_343])).
% 2.53/1.43  tff(c_10, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.43  tff(c_391, plain, (![B_109]: (B_109='#skF_4' | ~r1_tarski(B_109, '#skF_4'))), inference(resolution, [status(thm)], [c_349, c_10])).
% 2.53/1.43  tff(c_406, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_326, c_391])).
% 2.53/1.43  tff(c_412, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_28])).
% 2.53/1.43  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.43  tff(c_359, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_320, c_8])).
% 2.53/1.43  tff(c_367, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_40])).
% 2.53/1.43  tff(c_484, plain, (![A_119, B_120, C_121, D_122]: (r2_relset_1(A_119, B_120, C_121, C_121) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.43  tff(c_486, plain, (![C_121, D_122]: (r2_relset_1('#skF_2', '#skF_3', C_121, C_121) | ~m1_subset_1(D_122, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_359, c_484])).
% 2.53/1.43  tff(c_491, plain, (![C_121, D_122]: (r2_relset_1('#skF_2', '#skF_3', C_121, C_121) | ~m1_subset_1(D_122, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(C_121, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_486])).
% 2.53/1.43  tff(c_493, plain, (![D_122]: (~m1_subset_1(D_122, k1_zfmisc_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_491])).
% 2.53/1.43  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_367])).
% 2.53/1.43  tff(c_497, plain, (![C_123]: (r2_relset_1('#skF_2', '#skF_3', C_123, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_491])).
% 2.53/1.43  tff(c_499, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_367, c_497])).
% 2.53/1.43  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_499])).
% 2.53/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.43  
% 2.53/1.43  Inference rules
% 2.53/1.43  ----------------------
% 2.53/1.43  #Ref     : 0
% 2.53/1.43  #Sup     : 87
% 2.53/1.43  #Fact    : 0
% 2.53/1.43  #Define  : 0
% 2.53/1.43  #Split   : 9
% 2.53/1.43  #Chain   : 0
% 2.53/1.43  #Close   : 0
% 2.53/1.43  
% 2.53/1.43  Ordering : KBO
% 2.53/1.43  
% 2.53/1.43  Simplification rules
% 2.53/1.43  ----------------------
% 2.53/1.43  #Subsume      : 25
% 2.53/1.43  #Demod        : 88
% 2.53/1.43  #Tautology    : 43
% 2.53/1.43  #SimpNegUnit  : 7
% 2.53/1.43  #BackRed      : 25
% 2.53/1.43  
% 2.53/1.43  #Partial instantiations: 0
% 2.53/1.43  #Strategies tried      : 1
% 2.53/1.43  
% 2.53/1.43  Timing (in seconds)
% 2.53/1.43  ----------------------
% 2.60/1.43  Preprocessing        : 0.29
% 2.60/1.43  Parsing              : 0.15
% 2.60/1.43  CNF conversion       : 0.02
% 2.60/1.43  Main loop            : 0.27
% 2.60/1.43  Inferencing          : 0.10
% 2.60/1.43  Reduction            : 0.08
% 2.60/1.43  Demodulation         : 0.06
% 2.60/1.43  BG Simplification    : 0.01
% 2.60/1.43  Subsumption          : 0.05
% 2.60/1.43  Abstraction          : 0.01
% 2.60/1.43  MUC search           : 0.00
% 2.60/1.44  Cooper               : 0.00
% 2.60/1.44  Total                : 0.60
% 2.60/1.44  Index Insertion      : 0.00
% 2.60/1.44  Index Deletion       : 0.00
% 2.60/1.44  Index Matching       : 0.00
% 2.60/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
