%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:10 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 155 expanded)
%              Number of leaves         :   34 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 306 expanded)
%              Number of equality atoms :   36 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_40,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_78])).

tff(c_26,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) = k1_xboole_0
      | k1_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_26])).

tff(c_102,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_24,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | k2_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_24])).

tff(c_103,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_100])).

tff(c_137,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_137])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_273,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_292,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_273])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [C_44,A_45] :
      ( r2_hidden(C_44,k1_zfmisc_1(A_45))
      | ~ r1_tarski(C_44,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [C_44,A_45] :
      ( m1_subset_1(C_44,k1_zfmisc_1(A_45))
      | ~ r1_tarski(C_44,A_45) ) ),
    inference(resolution,[status(thm)],[c_54,c_16])).

tff(c_163,plain,(
    ! [A_73,C_74,B_75] :
      ( m1_subset_1(A_73,C_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(C_74))
      | ~ r2_hidden(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_186,plain,(
    ! [A_80,A_81,C_82] :
      ( m1_subset_1(A_80,A_81)
      | ~ r2_hidden(A_80,C_82)
      | ~ r1_tarski(C_82,A_81) ) ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_193,plain,(
    ! [A_83,A_84] :
      ( m1_subset_1('#skF_1'(A_83),A_84)
      | ~ r1_tarski(A_83,A_84)
      | k1_xboole_0 = A_83 ) ),
    inference(resolution,[status(thm)],[c_2,c_186])).

tff(c_69,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_48,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_104,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_215,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_193,c_104])).

tff(c_250,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_293,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_250])).

tff(c_302,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_293])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_151,c_302])).

tff(c_307,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_349,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_364,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_349])).

tff(c_369,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_364])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_369])).

tff(c_372,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_506,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_521,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_506])).

tff(c_526,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_521])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_526])).

tff(c_530,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_643,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_relset_1(A_185,B_186,C_187) = k1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_654,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_643])).

tff(c_658,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_654])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:30:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.47  
% 2.88/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.47  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.88/1.47  
% 2.88/1.47  %Foreground sorts:
% 2.88/1.47  
% 2.88/1.47  
% 2.88/1.47  %Background operators:
% 2.88/1.47  
% 2.88/1.47  
% 2.88/1.47  %Foreground operators:
% 2.88/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.88/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.88/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.88/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.88/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.88/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.88/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.47  
% 2.88/1.49  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.88/1.49  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.88/1.49  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.88/1.49  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.88/1.49  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.88/1.49  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.88/1.49  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.88/1.49  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.88/1.49  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.88/1.49  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.88/1.49  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.88/1.49  tff(c_40, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.49  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.49  tff(c_78, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.88/1.49  tff(c_92, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_78])).
% 2.88/1.49  tff(c_26, plain, (![A_15]: (k2_relat_1(A_15)=k1_xboole_0 | k1_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.88/1.49  tff(c_99, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_26])).
% 2.88/1.49  tff(c_102, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 2.88/1.49  tff(c_24, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | k2_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.88/1.49  tff(c_100, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_24])).
% 2.88/1.49  tff(c_103, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_102, c_100])).
% 2.88/1.49  tff(c_137, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.49  tff(c_151, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_137])).
% 2.88/1.49  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.88/1.49  tff(c_273, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.88/1.49  tff(c_292, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_273])).
% 2.88/1.49  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.49  tff(c_54, plain, (![C_44, A_45]: (r2_hidden(C_44, k1_zfmisc_1(A_45)) | ~r1_tarski(C_44, A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.49  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.49  tff(c_58, plain, (![C_44, A_45]: (m1_subset_1(C_44, k1_zfmisc_1(A_45)) | ~r1_tarski(C_44, A_45))), inference(resolution, [status(thm)], [c_54, c_16])).
% 2.88/1.49  tff(c_163, plain, (![A_73, C_74, B_75]: (m1_subset_1(A_73, C_74) | ~m1_subset_1(B_75, k1_zfmisc_1(C_74)) | ~r2_hidden(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.49  tff(c_186, plain, (![A_80, A_81, C_82]: (m1_subset_1(A_80, A_81) | ~r2_hidden(A_80, C_82) | ~r1_tarski(C_82, A_81))), inference(resolution, [status(thm)], [c_58, c_163])).
% 2.88/1.49  tff(c_193, plain, (![A_83, A_84]: (m1_subset_1('#skF_1'(A_83), A_84) | ~r1_tarski(A_83, A_84) | k1_xboole_0=A_83)), inference(resolution, [status(thm)], [c_2, c_186])).
% 2.88/1.49  tff(c_69, plain, (![D_48]: (~r2_hidden(D_48, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_48, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.88/1.49  tff(c_74, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.88/1.49  tff(c_104, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 2.88/1.49  tff(c_215, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_193, c_104])).
% 2.88/1.49  tff(c_250, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_215])).
% 2.88/1.49  tff(c_293, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_250])).
% 2.88/1.49  tff(c_302, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_293])).
% 2.88/1.49  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_151, c_302])).
% 2.88/1.49  tff(c_307, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_215])).
% 2.88/1.49  tff(c_349, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.88/1.49  tff(c_364, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_349])).
% 2.88/1.49  tff(c_369, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_307, c_364])).
% 2.88/1.49  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_369])).
% 2.88/1.49  tff(c_372, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 2.88/1.49  tff(c_506, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.88/1.49  tff(c_521, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_506])).
% 2.88/1.49  tff(c_526, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_372, c_521])).
% 2.88/1.49  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_526])).
% 2.88/1.49  tff(c_530, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 2.88/1.49  tff(c_643, plain, (![A_185, B_186, C_187]: (k1_relset_1(A_185, B_186, C_187)=k1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.88/1.49  tff(c_654, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_643])).
% 2.88/1.49  tff(c_658, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_530, c_654])).
% 2.88/1.49  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_658])).
% 2.88/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  Inference rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Ref     : 0
% 2.88/1.49  #Sup     : 121
% 2.88/1.49  #Fact    : 0
% 2.88/1.49  #Define  : 0
% 2.88/1.49  #Split   : 4
% 2.88/1.49  #Chain   : 0
% 2.88/1.49  #Close   : 0
% 2.88/1.49  
% 2.88/1.49  Ordering : KBO
% 2.88/1.49  
% 2.88/1.49  Simplification rules
% 2.88/1.49  ----------------------
% 2.88/1.49  #Subsume      : 1
% 2.88/1.49  #Demod        : 18
% 2.88/1.49  #Tautology    : 21
% 2.88/1.49  #SimpNegUnit  : 4
% 2.88/1.49  #BackRed      : 7
% 2.88/1.49  
% 2.88/1.49  #Partial instantiations: 0
% 2.88/1.49  #Strategies tried      : 1
% 2.88/1.49  
% 2.88/1.49  Timing (in seconds)
% 2.88/1.49  ----------------------
% 2.88/1.49  Preprocessing        : 0.34
% 2.88/1.49  Parsing              : 0.18
% 2.88/1.49  CNF conversion       : 0.02
% 2.88/1.49  Main loop            : 0.31
% 2.88/1.49  Inferencing          : 0.13
% 2.88/1.49  Reduction            : 0.09
% 2.88/1.49  Demodulation         : 0.05
% 2.88/1.49  BG Simplification    : 0.02
% 2.88/1.49  Subsumption          : 0.05
% 2.88/1.49  Abstraction          : 0.02
% 2.88/1.49  MUC search           : 0.00
% 2.88/1.49  Cooper               : 0.00
% 2.88/1.49  Total                : 0.69
% 2.88/1.49  Index Insertion      : 0.00
% 2.88/1.49  Index Deletion       : 0.00
% 2.88/1.49  Index Matching       : 0.00
% 2.88/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
