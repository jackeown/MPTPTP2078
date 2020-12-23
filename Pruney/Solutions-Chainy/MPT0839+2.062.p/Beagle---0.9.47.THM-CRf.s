%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 188 expanded)
%              Number of leaves         :   36 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 399 expanded)
%              Number of equality atoms :   26 (  70 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_18,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_119,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_119])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_122])).

tff(c_165,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_179,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_180,plain,(
    ! [B_71,A_72] :
      ( k7_relat_1(B_71,A_72) = B_71
      | ~ v4_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_183,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_180])).

tff(c_186,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_183])).

tff(c_260,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_274,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_260])).

tff(c_114,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_118,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1('#skF_1'(A_53,B_54),B_54)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_114,c_12])).

tff(c_10,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),A_2)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_138,plain,(
    ! [D_61] :
      ( ~ r2_hidden(D_61,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_61,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_223,plain,(
    ! [B_77] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_77),'#skF_3')
      | r1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_77) ) ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_228,plain,(
    r1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_223])).

tff(c_281,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_228])).

tff(c_24,plain,(
    ! [A_20] :
      ( k7_relat_1(A_20,k1_relat_1(A_20)) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_191,plain,(
    ! [C_73,A_74,B_75] :
      ( k7_relat_1(k7_relat_1(C_73,A_74),B_75) = k1_xboole_0
      | ~ r1_xboole_0(A_74,B_75)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_320,plain,(
    ! [A_92,B_93] :
      ( k7_relat_1(A_92,B_93) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(A_92),B_93)
      | ~ v1_relat_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_191])).

tff(c_323,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_320])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_186,c_323])).

tff(c_245,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_259,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_245])).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_275,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_36])).

tff(c_328,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_275])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_45] :
      ( v1_xboole_0(k2_relat_1(A_45))
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_55,plain,(
    ! [A_46] :
      ( k2_relat_1(A_46) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_63,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_332,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_63])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.18/1.32  
% 2.18/1.32  %Foreground sorts:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Background operators:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Foreground operators:
% 2.18/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.18/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.32  
% 2.18/1.33  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.33  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.18/1.33  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.33  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.18/1.33  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.18/1.33  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.56/1.33  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.56/1.33  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.56/1.33  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.56/1.33  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.56/1.33  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.56/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.56/1.33  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.56/1.33  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.56/1.33  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.33  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.56/1.33  tff(c_119, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.33  tff(c_122, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_119])).
% 2.56/1.33  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_122])).
% 2.56/1.33  tff(c_165, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.56/1.33  tff(c_179, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_165])).
% 2.56/1.33  tff(c_180, plain, (![B_71, A_72]: (k7_relat_1(B_71, A_72)=B_71 | ~v4_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.33  tff(c_183, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_179, c_180])).
% 2.56/1.33  tff(c_186, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_183])).
% 2.56/1.33  tff(c_260, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.56/1.33  tff(c_274, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_260])).
% 2.56/1.33  tff(c_114, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.56/1.33  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_118, plain, (![A_53, B_54]: (m1_subset_1('#skF_1'(A_53, B_54), B_54) | r1_xboole_0(A_53, B_54))), inference(resolution, [status(thm)], [c_114, c_12])).
% 2.56/1.33  tff(c_10, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), A_2) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.56/1.33  tff(c_138, plain, (![D_61]: (~r2_hidden(D_61, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_61, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.56/1.33  tff(c_223, plain, (![B_77]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_77), '#skF_3') | r1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_77))), inference(resolution, [status(thm)], [c_10, c_138])).
% 2.56/1.33  tff(c_228, plain, (r1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_118, c_223])).
% 2.56/1.33  tff(c_281, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_228])).
% 2.56/1.33  tff(c_24, plain, (![A_20]: (k7_relat_1(A_20, k1_relat_1(A_20))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.33  tff(c_191, plain, (![C_73, A_74, B_75]: (k7_relat_1(k7_relat_1(C_73, A_74), B_75)=k1_xboole_0 | ~r1_xboole_0(A_74, B_75) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.33  tff(c_320, plain, (![A_92, B_93]: (k7_relat_1(A_92, B_93)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(A_92), B_93) | ~v1_relat_1(A_92) | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_24, c_191])).
% 2.56/1.33  tff(c_323, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_281, c_320])).
% 2.56/1.33  tff(c_326, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_186, c_323])).
% 2.56/1.33  tff(c_245, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.56/1.33  tff(c_259, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_245])).
% 2.56/1.33  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.56/1.33  tff(c_275, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_259, c_36])).
% 2.56/1.33  tff(c_328, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_275])).
% 2.56/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.56/1.33  tff(c_50, plain, (![A_45]: (v1_xboole_0(k2_relat_1(A_45)) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.33  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.56/1.33  tff(c_55, plain, (![A_46]: (k2_relat_1(A_46)=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_50, c_4])).
% 2.56/1.33  tff(c_63, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_55])).
% 2.56/1.33  tff(c_332, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_63])).
% 2.56/1.33  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_332])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 63
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 0
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 2
% 2.56/1.33  #Demod        : 31
% 2.56/1.33  #Tautology    : 23
% 2.56/1.33  #SimpNegUnit  : 1
% 2.56/1.33  #BackRed      : 14
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.32
% 2.56/1.33  Parsing              : 0.17
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.22
% 2.56/1.33  Inferencing          : 0.09
% 2.56/1.33  Reduction            : 0.07
% 2.56/1.33  Demodulation         : 0.05
% 2.56/1.33  BG Simplification    : 0.01
% 2.56/1.33  Subsumption          : 0.03
% 2.56/1.33  Abstraction          : 0.01
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.57
% 2.56/1.34  Index Insertion      : 0.00
% 2.56/1.34  Index Deletion       : 0.00
% 2.56/1.34  Index Matching       : 0.00
% 2.56/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
