%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 242 expanded)
%              Number of equality atoms :   29 (  59 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_32,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_14,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) = k1_xboole_0
      | k1_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_73,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_14])).

tff(c_74,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_105,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_106,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_109,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_106])).

tff(c_112,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_109])).

tff(c_140,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(A_61,B_62)
      | ~ r2_hidden(A_61,k1_relat_1(k7_relat_1(C_63,B_62)))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_143,plain,(
    ! [A_61] :
      ( r2_hidden(A_61,'#skF_3')
      | ~ r2_hidden(A_61,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_140])).

tff(c_151,plain,(
    ! [A_64] :
      ( r2_hidden(A_64,'#skF_3')
      | ~ r2_hidden(A_64,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_143])).

tff(c_155,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_151])).

tff(c_158,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_155])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_4])).

tff(c_190,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_199,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_190])).

tff(c_52,plain,(
    ! [D_44] :
      ( ~ r2_hidden(D_44,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_44,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_57,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_163,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_218,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_163])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_218])).

tff(c_223,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_238,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_245,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_238])).

tff(c_248,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_245])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_248])).

tff(c_251,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_356,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_363,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_356])).

tff(c_366,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_363])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.19/1.29  
% 2.19/1.29  %Foreground sorts:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Background operators:
% 2.19/1.29  
% 2.19/1.29  
% 2.19/1.29  %Foreground operators:
% 2.19/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.29  
% 2.47/1.31  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.47/1.31  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.47/1.31  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.47/1.31  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.47/1.31  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.31  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.31  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.47/1.31  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.47/1.31  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.47/1.31  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.47/1.31  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.47/1.31  tff(c_32, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.31  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_58, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.31  tff(c_65, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.47/1.31  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_65])).
% 2.47/1.31  tff(c_14, plain, (![A_12]: (k2_relat_1(A_12)=k1_xboole_0 | k1_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.31  tff(c_73, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_14])).
% 2.47/1.31  tff(c_74, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_73])).
% 2.47/1.31  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.31  tff(c_96, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.31  tff(c_105, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_96])).
% 2.47/1.31  tff(c_106, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.31  tff(c_109, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_105, c_106])).
% 2.47/1.31  tff(c_112, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_109])).
% 2.47/1.31  tff(c_140, plain, (![A_61, B_62, C_63]: (r2_hidden(A_61, B_62) | ~r2_hidden(A_61, k1_relat_1(k7_relat_1(C_63, B_62))) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.47/1.31  tff(c_143, plain, (![A_61]: (r2_hidden(A_61, '#skF_3') | ~r2_hidden(A_61, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_140])).
% 2.47/1.31  tff(c_151, plain, (![A_64]: (r2_hidden(A_64, '#skF_3') | ~r2_hidden(A_64, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_143])).
% 2.47/1.31  tff(c_155, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_151])).
% 2.47/1.31  tff(c_158, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_155])).
% 2.47/1.31  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.31  tff(c_162, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_158, c_4])).
% 2.47/1.31  tff(c_190, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.31  tff(c_199, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_190])).
% 2.47/1.31  tff(c_52, plain, (![D_44]: (~r2_hidden(D_44, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_44, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.47/1.31  tff(c_57, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.47/1.31  tff(c_163, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_57])).
% 2.47/1.31  tff(c_218, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_163])).
% 2.47/1.31  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_218])).
% 2.47/1.31  tff(c_223, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_57])).
% 2.47/1.31  tff(c_238, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.31  tff(c_245, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_238])).
% 2.47/1.31  tff(c_248, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_223, c_245])).
% 2.47/1.31  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_248])).
% 2.47/1.31  tff(c_251, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_73])).
% 2.47/1.31  tff(c_356, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.31  tff(c_363, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_356])).
% 2.47/1.31  tff(c_366, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_251, c_363])).
% 2.47/1.31  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_366])).
% 2.47/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.31  
% 2.47/1.31  Inference rules
% 2.47/1.31  ----------------------
% 2.47/1.31  #Ref     : 0
% 2.47/1.31  #Sup     : 66
% 2.47/1.31  #Fact    : 0
% 2.47/1.31  #Define  : 0
% 2.47/1.31  #Split   : 3
% 2.47/1.31  #Chain   : 0
% 2.47/1.31  #Close   : 0
% 2.47/1.31  
% 2.47/1.31  Ordering : KBO
% 2.47/1.31  
% 2.47/1.31  Simplification rules
% 2.47/1.31  ----------------------
% 2.47/1.31  #Subsume      : 1
% 2.47/1.31  #Demod        : 21
% 2.47/1.31  #Tautology    : 26
% 2.47/1.31  #SimpNegUnit  : 4
% 2.47/1.31  #BackRed      : 4
% 2.47/1.31  
% 2.47/1.31  #Partial instantiations: 0
% 2.47/1.31  #Strategies tried      : 1
% 2.47/1.31  
% 2.47/1.31  Timing (in seconds)
% 2.47/1.31  ----------------------
% 2.47/1.31  Preprocessing        : 0.30
% 2.47/1.31  Parsing              : 0.16
% 2.47/1.31  CNF conversion       : 0.02
% 2.47/1.31  Main loop            : 0.23
% 2.47/1.31  Inferencing          : 0.09
% 2.47/1.31  Reduction            : 0.07
% 2.47/1.31  Demodulation         : 0.05
% 2.47/1.31  BG Simplification    : 0.01
% 2.47/1.31  Subsumption          : 0.03
% 2.47/1.31  Abstraction          : 0.01
% 2.47/1.31  MUC search           : 0.00
% 2.47/1.31  Cooper               : 0.00
% 2.47/1.31  Total                : 0.57
% 2.47/1.31  Index Insertion      : 0.00
% 2.47/1.31  Index Deletion       : 0.00
% 2.47/1.31  Index Matching       : 0.00
% 2.47/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
