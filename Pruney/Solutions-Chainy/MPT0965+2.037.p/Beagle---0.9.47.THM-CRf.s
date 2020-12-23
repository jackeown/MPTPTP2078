%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:05 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   66 (  84 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 172 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_83,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_87,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_83])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_93,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_162,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_162])).

tff(c_168,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_97,c_165])).

tff(c_169,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_168])).

tff(c_12,plain,(
    ! [C_14,B_13,A_12] :
      ( m1_subset_1(k1_funct_1(C_14,B_13),A_12)
      | ~ r2_hidden(B_13,k1_relat_1(C_14))
      | ~ v1_funct_1(C_14)
      | ~ v5_relat_1(C_14,A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_13),A_12)
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_12)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_12])).

tff(c_183,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_120),A_121)
      | ~ r2_hidden(B_120,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48,c_173])).

tff(c_66,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,B_50)
      | v1_xboole_0(B_50)
      | ~ m1_subset_1(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_38])).

tff(c_75,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_222,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_183,c_75])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_42,c_222])).

tff(c_236,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_55,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_2'(A_46),A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_247,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_236,c_59])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 20:27:45 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.05/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.05/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.30  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.30  
% 2.05/1.31  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.05/1.31  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.05/1.31  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.05/1.31  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.05/1.31  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.05/1.31  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.05/1.31  tff(f_56, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.05/1.31  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.05/1.31  tff(f_82, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.05/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.05/1.31  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.05/1.31  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.05/1.31  tff(c_83, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.31  tff(c_87, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_83])).
% 2.05/1.31  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.05/1.31  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.31  tff(c_76, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.05/1.31  tff(c_79, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_76])).
% 2.05/1.31  tff(c_82, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_79])).
% 2.05/1.31  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.05/1.31  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.05/1.31  tff(c_93, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.05/1.31  tff(c_97, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_93])).
% 2.05/1.31  tff(c_162, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.05/1.31  tff(c_165, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_162])).
% 2.05/1.31  tff(c_168, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_97, c_165])).
% 2.05/1.31  tff(c_169, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_168])).
% 2.05/1.31  tff(c_12, plain, (![C_14, B_13, A_12]: (m1_subset_1(k1_funct_1(C_14, B_13), A_12) | ~r2_hidden(B_13, k1_relat_1(C_14)) | ~v1_funct_1(C_14) | ~v5_relat_1(C_14, A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.31  tff(c_173, plain, (![B_13, A_12]: (m1_subset_1(k1_funct_1('#skF_6', B_13), A_12) | ~r2_hidden(B_13, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_12) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_12])).
% 2.05/1.31  tff(c_183, plain, (![B_120, A_121]: (m1_subset_1(k1_funct_1('#skF_6', B_120), A_121) | ~r2_hidden(B_120, '#skF_3') | ~v5_relat_1('#skF_6', A_121))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48, c_173])).
% 2.05/1.31  tff(c_66, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50) | v1_xboole_0(B_50) | ~m1_subset_1(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.31  tff(c_38, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.05/1.31  tff(c_74, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_66, c_38])).
% 2.05/1.31  tff(c_75, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 2.05/1.31  tff(c_222, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_183, c_75])).
% 2.05/1.31  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_42, c_222])).
% 2.05/1.31  tff(c_236, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 2.05/1.31  tff(c_55, plain, (![A_46]: (r2_hidden('#skF_2'(A_46), A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.31  tff(c_59, plain, (![A_46]: (~v1_xboole_0(A_46) | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.05/1.31  tff(c_247, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_236, c_59])).
% 2.05/1.31  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_247])).
% 2.05/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.31  
% 2.05/1.31  Inference rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Ref     : 0
% 2.05/1.31  #Sup     : 41
% 2.05/1.31  #Fact    : 0
% 2.05/1.31  #Define  : 0
% 2.05/1.31  #Split   : 3
% 2.05/1.31  #Chain   : 0
% 2.05/1.31  #Close   : 0
% 2.05/1.31  
% 2.05/1.31  Ordering : KBO
% 2.05/1.31  
% 2.05/1.31  Simplification rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Subsume      : 0
% 2.05/1.31  #Demod        : 11
% 2.05/1.31  #Tautology    : 9
% 2.05/1.31  #SimpNegUnit  : 3
% 2.05/1.31  #BackRed      : 1
% 2.05/1.31  
% 2.05/1.31  #Partial instantiations: 0
% 2.05/1.31  #Strategies tried      : 1
% 2.05/1.31  
% 2.05/1.31  Timing (in seconds)
% 2.05/1.31  ----------------------
% 2.05/1.31  Preprocessing        : 0.34
% 2.05/1.31  Parsing              : 0.18
% 2.05/1.31  CNF conversion       : 0.02
% 2.05/1.31  Main loop            : 0.20
% 2.05/1.32  Inferencing          : 0.08
% 2.05/1.32  Reduction            : 0.06
% 2.05/1.32  Demodulation         : 0.04
% 2.05/1.32  BG Simplification    : 0.01
% 2.05/1.32  Subsumption          : 0.03
% 2.05/1.32  Abstraction          : 0.01
% 2.05/1.32  MUC search           : 0.00
% 2.05/1.32  Cooper               : 0.00
% 2.05/1.32  Total                : 0.57
% 2.05/1.32  Index Insertion      : 0.00
% 2.05/1.32  Index Deletion       : 0.00
% 2.05/1.32  Index Matching       : 0.00
% 2.05/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
