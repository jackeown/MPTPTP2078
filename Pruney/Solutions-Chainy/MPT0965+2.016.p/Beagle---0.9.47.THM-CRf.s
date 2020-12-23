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
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   58 (  71 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 140 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_47,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_46,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_53,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_53])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_63,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_147,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_154,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_147])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_67,c_154])).

tff(c_159,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_158])).

tff(c_73,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_77,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_82,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k2_relset_1(A_74,B_75,C_76),k1_zfmisc_1(B_75))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_97,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_82])).

tff(c_102,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_97])).

tff(c_109,plain,(
    ! [A_79,D_80] :
      ( r2_hidden(k1_funct_1(A_79,D_80),k2_relat_1(A_79))
      | ~ r2_hidden(D_80,k1_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_218,plain,(
    ! [A_109,D_110,A_111] :
      ( r2_hidden(k1_funct_1(A_109,D_110),A_111)
      | ~ m1_subset_1(k2_relat_1(A_109),k1_zfmisc_1(A_111))
      | ~ r2_hidden(D_110,k1_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_220,plain,(
    ! [D_110] :
      ( r2_hidden(k1_funct_1('#skF_8',D_110),'#skF_6')
      | ~ r2_hidden(D_110,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_102,c_218])).

tff(c_239,plain,(
    ! [D_114] :
      ( r2_hidden(k1_funct_1('#skF_8',D_114),'#skF_6')
      | ~ r2_hidden(D_114,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_52,c_159,c_220])).

tff(c_42,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_239,c_42])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:23:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.15/1.30  
% 2.15/1.30  %Foreground sorts:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Background operators:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Foreground operators:
% 2.15/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.15/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.15/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.15/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.15/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.15/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.30  
% 2.15/1.32  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.15/1.32  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.15/1.32  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.15/1.32  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.15/1.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.15/1.32  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.15/1.32  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.15/1.32  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.15/1.32  tff(c_46, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.32  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.32  tff(c_53, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.32  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_53])).
% 2.15/1.32  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.32  tff(c_44, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.32  tff(c_50, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.32  tff(c_63, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.32  tff(c_67, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_63])).
% 2.15/1.32  tff(c_147, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.15/1.32  tff(c_154, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_147])).
% 2.15/1.32  tff(c_158, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_67, c_154])).
% 2.15/1.32  tff(c_159, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_44, c_158])).
% 2.15/1.32  tff(c_73, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.32  tff(c_77, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_73])).
% 2.15/1.32  tff(c_82, plain, (![A_74, B_75, C_76]: (m1_subset_1(k2_relset_1(A_74, B_75, C_76), k1_zfmisc_1(B_75)) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.32  tff(c_97, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_77, c_82])).
% 2.15/1.32  tff(c_102, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_97])).
% 2.15/1.32  tff(c_109, plain, (![A_79, D_80]: (r2_hidden(k1_funct_1(A_79, D_80), k2_relat_1(A_79)) | ~r2_hidden(D_80, k1_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.32  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.32  tff(c_218, plain, (![A_109, D_110, A_111]: (r2_hidden(k1_funct_1(A_109, D_110), A_111) | ~m1_subset_1(k2_relat_1(A_109), k1_zfmisc_1(A_111)) | ~r2_hidden(D_110, k1_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_109, c_2])).
% 2.15/1.32  tff(c_220, plain, (![D_110]: (r2_hidden(k1_funct_1('#skF_8', D_110), '#skF_6') | ~r2_hidden(D_110, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_102, c_218])).
% 2.15/1.32  tff(c_239, plain, (![D_114]: (r2_hidden(k1_funct_1('#skF_8', D_114), '#skF_6') | ~r2_hidden(D_114, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_52, c_159, c_220])).
% 2.15/1.32  tff(c_42, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.32  tff(c_244, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_239, c_42])).
% 2.15/1.32  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_244])).
% 2.15/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  Inference rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Ref     : 0
% 2.15/1.32  #Sup     : 46
% 2.15/1.32  #Fact    : 0
% 2.15/1.32  #Define  : 0
% 2.15/1.32  #Split   : 0
% 2.15/1.32  #Chain   : 0
% 2.15/1.32  #Close   : 0
% 2.15/1.32  
% 2.15/1.32  Ordering : KBO
% 2.15/1.32  
% 2.15/1.32  Simplification rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Subsume      : 0
% 2.15/1.32  #Demod        : 14
% 2.15/1.32  #Tautology    : 14
% 2.15/1.32  #SimpNegUnit  : 2
% 2.15/1.32  #BackRed      : 1
% 2.15/1.32  
% 2.15/1.32  #Partial instantiations: 0
% 2.15/1.32  #Strategies tried      : 1
% 2.15/1.32  
% 2.15/1.32  Timing (in seconds)
% 2.15/1.32  ----------------------
% 2.15/1.32  Preprocessing        : 0.33
% 2.15/1.32  Parsing              : 0.17
% 2.15/1.32  CNF conversion       : 0.03
% 2.15/1.32  Main loop            : 0.21
% 2.15/1.32  Inferencing          : 0.08
% 2.15/1.32  Reduction            : 0.06
% 2.15/1.32  Demodulation         : 0.04
% 2.15/1.32  BG Simplification    : 0.02
% 2.15/1.32  Subsumption          : 0.04
% 2.15/1.32  Abstraction          : 0.01
% 2.15/1.32  MUC search           : 0.00
% 2.15/1.32  Cooper               : 0.00
% 2.15/1.32  Total                : 0.57
% 2.15/1.32  Index Insertion      : 0.00
% 2.15/1.32  Index Deletion       : 0.00
% 2.15/1.32  Index Matching       : 0.00
% 2.15/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
