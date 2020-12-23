%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 108 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  112 ( 263 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_67,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_21] :
      ( v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k2_zfmisc_1(A_21,A_21)) ) ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_76,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_12,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_231,plain,(
    ! [B_69,A_70] :
      ( k5_relat_1(B_69,k6_relat_1(A_70)) = B_69
      | ~ r1_tarski(k2_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_243,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_231])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_73,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_79,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_73])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_81,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_153,plain,(
    ! [B_60,A_61] :
      ( k1_relat_1(B_60) = A_61
      | ~ v1_partfun1(B_60,A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_159,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_153])).

tff(c_165,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_159])).

tff(c_166,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_205,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_211,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_205])).

tff(c_216,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_211])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_166,c_216])).

tff(c_219,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_362,plain,(
    ! [C_80,B_81,A_82] :
      ( k1_relat_1(k5_relat_1(C_80,B_81)) = k1_relat_1(k5_relat_1(C_80,A_82))
      | k1_relat_1(B_81) != k1_relat_1(A_82)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_383,plain,(
    ! [B_81] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_81)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_81) != k1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_32])).

tff(c_443,plain,(
    ! [B_83] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_83)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_83) != '#skF_1'
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_38,c_219,c_383])).

tff(c_455,plain,(
    ! [A_4] :
      ( k1_relat_1(k6_relat_1(A_4)) != '#skF_1'
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v5_relat_1('#skF_3',A_4)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_443])).

tff(c_470,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_76,c_12,c_455])).

tff(c_36,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.33  
% 2.35/1.33  %Foreground sorts:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Background operators:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Foreground operators:
% 2.35/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.35/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.35/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.35/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.35/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.33  
% 2.35/1.35  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 2.35/1.35  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.35  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 2.35/1.35  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.35/1.35  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.35/1.35  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.35/1.35  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.35/1.35  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.35/1.35  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.35/1.35  tff(f_84, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.35/1.35  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 2.35/1.35  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.35/1.35  tff(c_22, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.35  tff(c_67, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.35/1.35  tff(c_70, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k2_zfmisc_1(A_21, A_21)))), inference(resolution, [status(thm)], [c_22, c_67])).
% 2.35/1.35  tff(c_76, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_70])).
% 2.35/1.35  tff(c_12, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.35  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.35/1.35  tff(c_231, plain, (![B_69, A_70]: (k5_relat_1(B_69, k6_relat_1(A_70))=B_69 | ~r1_tarski(k2_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.35  tff(c_243, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_231])).
% 2.35/1.35  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_73, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.35/1.35  tff(c_79, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_73])).
% 2.35/1.35  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_81, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.35  tff(c_89, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_81])).
% 2.35/1.35  tff(c_153, plain, (![B_60, A_61]: (k1_relat_1(B_60)=A_61 | ~v1_partfun1(B_60, A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.35/1.35  tff(c_159, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_89, c_153])).
% 2.35/1.35  tff(c_165, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_159])).
% 2.35/1.35  tff(c_166, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_165])).
% 2.35/1.35  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_42, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_205, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.35/1.35  tff(c_211, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_205])).
% 2.35/1.35  tff(c_216, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_211])).
% 2.35/1.35  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_166, c_216])).
% 2.35/1.35  tff(c_219, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_165])).
% 2.35/1.35  tff(c_362, plain, (![C_80, B_81, A_82]: (k1_relat_1(k5_relat_1(C_80, B_81))=k1_relat_1(k5_relat_1(C_80, A_82)) | k1_relat_1(B_81)!=k1_relat_1(A_82) | ~v1_relat_1(C_80) | ~v1_relat_1(B_81) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.35/1.35  tff(c_32, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_383, plain, (![B_81]: (k1_relat_1(k5_relat_1('#skF_3', B_81))!=k1_relat_1('#skF_3') | k1_relat_1(B_81)!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_81) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_362, c_32])).
% 2.35/1.35  tff(c_443, plain, (![B_83]: (k1_relat_1(k5_relat_1('#skF_3', B_83))!=k1_relat_1('#skF_3') | k1_relat_1(B_83)!='#skF_1' | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_38, c_219, c_383])).
% 2.35/1.35  tff(c_455, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))!='#skF_1' | ~v1_relat_1(k6_relat_1(A_4)) | ~v5_relat_1('#skF_3', A_4) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_443])).
% 2.35/1.35  tff(c_470, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_76, c_12, c_455])).
% 2.35/1.35  tff(c_36, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.35/1.35  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_36])).
% 2.35/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.35  
% 2.35/1.35  Inference rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Ref     : 0
% 2.35/1.35  #Sup     : 82
% 2.35/1.35  #Fact    : 0
% 2.35/1.35  #Define  : 0
% 2.35/1.35  #Split   : 1
% 2.35/1.35  #Chain   : 0
% 2.35/1.35  #Close   : 0
% 2.35/1.35  
% 2.35/1.35  Ordering : KBO
% 2.35/1.35  
% 2.35/1.35  Simplification rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Subsume      : 0
% 2.35/1.35  #Demod        : 83
% 2.35/1.35  #Tautology    : 38
% 2.35/1.35  #SimpNegUnit  : 3
% 2.35/1.35  #BackRed      : 1
% 2.35/1.35  
% 2.35/1.35  #Partial instantiations: 0
% 2.35/1.35  #Strategies tried      : 1
% 2.35/1.35  
% 2.35/1.35  Timing (in seconds)
% 2.35/1.35  ----------------------
% 2.35/1.35  Preprocessing        : 0.30
% 2.35/1.35  Parsing              : 0.17
% 2.35/1.35  CNF conversion       : 0.02
% 2.35/1.35  Main loop            : 0.28
% 2.35/1.35  Inferencing          : 0.11
% 2.35/1.35  Reduction            : 0.08
% 2.35/1.35  Demodulation         : 0.06
% 2.35/1.35  BG Simplification    : 0.02
% 2.35/1.35  Subsumption          : 0.04
% 2.35/1.35  Abstraction          : 0.01
% 2.35/1.35  MUC search           : 0.00
% 2.35/1.35  Cooper               : 0.00
% 2.35/1.35  Total                : 0.61
% 2.35/1.35  Index Insertion      : 0.00
% 2.35/1.35  Index Deletion       : 0.00
% 2.35/1.35  Index Matching       : 0.00
% 2.35/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
