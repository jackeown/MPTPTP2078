%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 105 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 190 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_88,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_91])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_225,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_239,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_225])).

tff(c_64,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1('#skF_1'(A_49,B_50),A_49)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_48,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_108,plain,(
    ! [A_61] :
      ( ~ m1_subset_1('#skF_1'(A_61,k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
      | r1_xboole_0(A_61,k1_relset_1('#skF_3','#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_113,plain,(
    r1_xboole_0('#skF_3',k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_73,c_108])).

tff(c_243,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_113])).

tff(c_117,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_131,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_117])).

tff(c_132,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_135,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_132])).

tff(c_138,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_135])).

tff(c_196,plain,(
    ! [C_74,A_75,B_76] :
      ( k7_relat_1(k7_relat_1(C_74,A_75),B_76) = k1_xboole_0
      | ~ r1_xboole_0(A_75,B_76)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_214,plain,(
    ! [B_76] :
      ( k7_relat_1('#skF_4',B_76) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_76)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_196])).

tff(c_219,plain,(
    ! [B_76] :
      ( k7_relat_1('#skF_4',B_76) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_214])).

tff(c_258,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_243,c_219])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_277,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_16])).

tff(c_283,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_22,c_277])).

tff(c_14,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_288,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_14])).

tff(c_295,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_288])).

tff(c_309,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_320,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_309])).

tff(c_324,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_320])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.32  
% 2.31/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.32  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.31/1.32  
% 2.31/1.32  %Foreground sorts:
% 2.31/1.32  
% 2.31/1.32  
% 2.31/1.32  %Background operators:
% 2.31/1.32  
% 2.31/1.32  
% 2.31/1.32  %Foreground operators:
% 2.31/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.31/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.31/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.31/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.31/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.31/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.32  
% 2.55/1.33  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.55/1.33  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.55/1.33  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.55/1.33  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.55/1.33  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.55/1.33  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.55/1.33  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.55/1.33  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.33  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.55/1.33  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.55/1.33  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.55/1.33  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.55/1.33  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.55/1.33  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.55/1.33  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.55/1.33  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.55/1.33  tff(c_88, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.33  tff(c_91, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_88])).
% 2.55/1.33  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_91])).
% 2.55/1.33  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.33  tff(c_225, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.33  tff(c_239, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_225])).
% 2.55/1.33  tff(c_64, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.33  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.33  tff(c_73, plain, (![A_49, B_50]: (m1_subset_1('#skF_1'(A_49, B_50), A_49) | r1_xboole_0(A_49, B_50))), inference(resolution, [status(thm)], [c_64, c_8])).
% 2.55/1.33  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.33  tff(c_58, plain, (![D_48]: (~r2_hidden(D_48, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_48, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.55/1.33  tff(c_108, plain, (![A_61]: (~m1_subset_1('#skF_1'(A_61, k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | r1_xboole_0(A_61, k1_relset_1('#skF_3', '#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.55/1.33  tff(c_113, plain, (r1_xboole_0('#skF_3', k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_73, c_108])).
% 2.55/1.33  tff(c_243, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_113])).
% 2.55/1.33  tff(c_117, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.55/1.33  tff(c_131, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_117])).
% 2.55/1.33  tff(c_132, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.55/1.33  tff(c_135, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_131, c_132])).
% 2.55/1.33  tff(c_138, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_135])).
% 2.55/1.33  tff(c_196, plain, (![C_74, A_75, B_76]: (k7_relat_1(k7_relat_1(C_74, A_75), B_76)=k1_xboole_0 | ~r1_xboole_0(A_75, B_76) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.55/1.33  tff(c_214, plain, (![B_76]: (k7_relat_1('#skF_4', B_76)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_76) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_196])).
% 2.55/1.33  tff(c_219, plain, (![B_76]: (k7_relat_1('#skF_4', B_76)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_76))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_214])).
% 2.55/1.33  tff(c_258, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_243, c_219])).
% 2.55/1.33  tff(c_16, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.33  tff(c_277, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_258, c_16])).
% 2.55/1.33  tff(c_283, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_22, c_277])).
% 2.55/1.33  tff(c_14, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.55/1.33  tff(c_288, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_283, c_14])).
% 2.55/1.33  tff(c_295, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_288])).
% 2.55/1.33  tff(c_309, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.55/1.33  tff(c_320, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_309])).
% 2.55/1.33  tff(c_324, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_295, c_320])).
% 2.55/1.33  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_324])).
% 2.55/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  Inference rules
% 2.55/1.33  ----------------------
% 2.55/1.33  #Ref     : 0
% 2.55/1.33  #Sup     : 66
% 2.55/1.33  #Fact    : 0
% 2.55/1.33  #Define  : 0
% 2.55/1.33  #Split   : 1
% 2.55/1.33  #Chain   : 0
% 2.55/1.33  #Close   : 0
% 2.55/1.33  
% 2.55/1.33  Ordering : KBO
% 2.55/1.33  
% 2.55/1.33  Simplification rules
% 2.55/1.33  ----------------------
% 2.55/1.34  #Subsume      : 1
% 2.55/1.34  #Demod        : 22
% 2.55/1.34  #Tautology    : 25
% 2.55/1.34  #SimpNegUnit  : 1
% 2.55/1.34  #BackRed      : 7
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.34  Preprocessing        : 0.33
% 2.55/1.34  Parsing              : 0.18
% 2.55/1.34  CNF conversion       : 0.02
% 2.55/1.34  Main loop            : 0.23
% 2.55/1.34  Inferencing          : 0.09
% 2.55/1.34  Reduction            : 0.07
% 2.55/1.34  Demodulation         : 0.05
% 2.55/1.34  BG Simplification    : 0.01
% 2.55/1.34  Subsumption          : 0.03
% 2.55/1.34  Abstraction          : 0.01
% 2.55/1.34  MUC search           : 0.00
% 2.55/1.34  Cooper               : 0.00
% 2.55/1.34  Total                : 0.59
% 2.55/1.34  Index Insertion      : 0.00
% 2.55/1.34  Index Deletion       : 0.00
% 2.55/1.34  Index Matching       : 0.00
% 2.55/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
