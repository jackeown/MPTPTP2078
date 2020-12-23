%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:05 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   66 (  84 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 175 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_87,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_81,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_91,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_117,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_95,c_120])).

tff(c_124,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_123])).

tff(c_12,plain,(
    ! [C_14,B_13,A_12] :
      ( m1_subset_1(k1_funct_1(C_14,B_13),A_12)
      | ~ r2_hidden(B_13,k1_relat_1(C_14))
      | ~ v1_funct_1(C_14)
      | ~ v5_relat_1(C_14,A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_13),A_12)
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_12)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_138,plain,(
    ! [B_79,A_80] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_79),A_80)
      | ~ r2_hidden(B_79,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_46,c_128])).

tff(c_64,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_71,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_36])).

tff(c_73,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_173,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_73])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_173])).

tff(c_186,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_53,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_2'(A_50),A_50)
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(A_50)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_190,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_186,c_57])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.33  
% 1.84/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 1.84/1.33  
% 1.84/1.33  %Foreground sorts:
% 1.84/1.33  
% 1.84/1.33  
% 1.84/1.33  %Background operators:
% 1.84/1.33  
% 1.84/1.33  
% 1.84/1.33  %Foreground operators:
% 1.84/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.84/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.84/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.84/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.33  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.84/1.33  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.84/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.84/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.84/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.84/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.33  
% 2.14/1.35  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.14/1.35  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.35  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.14/1.35  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.14/1.35  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.14/1.35  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.14/1.35  tff(f_56, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 2.14/1.35  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.14/1.35  tff(f_87, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.14/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.35  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.14/1.35  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.14/1.35  tff(c_81, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.35  tff(c_85, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_81])).
% 2.14/1.35  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.14/1.35  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.35  tff(c_74, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.35  tff(c_77, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_74])).
% 2.14/1.35  tff(c_80, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 2.14/1.35  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.14/1.35  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.14/1.35  tff(c_91, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.35  tff(c_95, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_91])).
% 2.14/1.35  tff(c_117, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.14/1.35  tff(c_120, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_117])).
% 2.14/1.35  tff(c_123, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_95, c_120])).
% 2.14/1.35  tff(c_124, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_123])).
% 2.14/1.35  tff(c_12, plain, (![C_14, B_13, A_12]: (m1_subset_1(k1_funct_1(C_14, B_13), A_12) | ~r2_hidden(B_13, k1_relat_1(C_14)) | ~v1_funct_1(C_14) | ~v5_relat_1(C_14, A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.35  tff(c_128, plain, (![B_13, A_12]: (m1_subset_1(k1_funct_1('#skF_6', B_13), A_12) | ~r2_hidden(B_13, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_12) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 2.14/1.35  tff(c_138, plain, (![B_79, A_80]: (m1_subset_1(k1_funct_1('#skF_6', B_79), A_80) | ~r2_hidden(B_79, '#skF_3') | ~v5_relat_1('#skF_6', A_80))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_46, c_128])).
% 2.14/1.35  tff(c_64, plain, (![A_53, B_54]: (r2_hidden(A_53, B_54) | v1_xboole_0(B_54) | ~m1_subset_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.35  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.14/1.35  tff(c_71, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_64, c_36])).
% 2.14/1.35  tff(c_73, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_71])).
% 2.14/1.35  tff(c_173, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_138, c_73])).
% 2.14/1.35  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_173])).
% 2.14/1.35  tff(c_186, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_71])).
% 2.14/1.35  tff(c_53, plain, (![A_50]: (r2_hidden('#skF_2'(A_50), A_50) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.35  tff(c_57, plain, (![A_50]: (~v1_xboole_0(A_50) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.14/1.35  tff(c_190, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_186, c_57])).
% 2.14/1.35  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_190])).
% 2.14/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.35  
% 2.14/1.35  Inference rules
% 2.14/1.35  ----------------------
% 2.14/1.35  #Ref     : 0
% 2.14/1.35  #Sup     : 30
% 2.14/1.35  #Fact    : 0
% 2.14/1.35  #Define  : 0
% 2.14/1.35  #Split   : 1
% 2.14/1.35  #Chain   : 0
% 2.14/1.35  #Close   : 0
% 2.14/1.35  
% 2.14/1.35  Ordering : KBO
% 2.14/1.35  
% 2.14/1.35  Simplification rules
% 2.14/1.35  ----------------------
% 2.14/1.35  #Subsume      : 0
% 2.14/1.35  #Demod        : 8
% 2.14/1.35  #Tautology    : 8
% 2.14/1.35  #SimpNegUnit  : 2
% 2.14/1.35  #BackRed      : 1
% 2.14/1.35  
% 2.14/1.35  #Partial instantiations: 0
% 2.14/1.35  #Strategies tried      : 1
% 2.14/1.35  
% 2.14/1.35  Timing (in seconds)
% 2.14/1.35  ----------------------
% 2.14/1.35  Preprocessing        : 0.32
% 2.14/1.35  Parsing              : 0.15
% 2.14/1.35  CNF conversion       : 0.02
% 2.14/1.35  Main loop            : 0.16
% 2.14/1.35  Inferencing          : 0.06
% 2.14/1.35  Reduction            : 0.05
% 2.14/1.35  Demodulation         : 0.04
% 2.14/1.35  BG Simplification    : 0.01
% 2.14/1.35  Subsumption          : 0.02
% 2.14/1.35  Abstraction          : 0.01
% 2.14/1.35  MUC search           : 0.00
% 2.14/1.35  Cooper               : 0.00
% 2.14/1.35  Total                : 0.51
% 2.14/1.35  Index Insertion      : 0.00
% 2.14/1.35  Index Deletion       : 0.00
% 2.14/1.35  Index Matching       : 0.00
% 2.14/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
