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

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   66 (  84 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 172 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

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
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
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
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
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

tff(c_125,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_155,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_155])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_129,c_158])).

tff(c_162,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_161])).

tff(c_12,plain,(
    ! [C_14,B_13,A_12] :
      ( m1_subset_1(k1_funct_1(C_14,B_13),A_12)
      | ~ r2_hidden(B_13,k1_relat_1(C_14))
      | ~ v1_funct_1(C_14)
      | ~ v5_relat_1(C_14,A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_13),A_12)
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_12)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_12])).

tff(c_176,plain,(
    ! [B_103,A_104] :
      ( m1_subset_1(k1_funct_1('#skF_6',B_103),A_104)
      | ~ r2_hidden(B_103,'#skF_3')
      | ~ v5_relat_1('#skF_6',A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48,c_166])).

tff(c_66,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
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

tff(c_211,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_75])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_42,c_211])).

tff(c_224,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_55,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_2'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_228,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_224,c_59])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.19/1.27  
% 2.19/1.27  %Foreground sorts:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Background operators:
% 2.19/1.27  
% 2.19/1.27  
% 2.19/1.27  %Foreground operators:
% 2.19/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.27  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.19/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.19/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.27  
% 2.19/1.28  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.19/1.28  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.19/1.28  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.19/1.28  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.19/1.28  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.19/1.28  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.19/1.28  tff(f_56, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.19/1.28  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.19/1.28  tff(f_82, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.19/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.28  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.28  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.28  tff(c_83, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.28  tff(c_87, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_83])).
% 2.19/1.28  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.28  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.28  tff(c_76, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.28  tff(c_79, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_76])).
% 2.19/1.28  tff(c_82, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_79])).
% 2.19/1.28  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.28  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.28  tff(c_125, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.28  tff(c_129, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_125])).
% 2.19/1.28  tff(c_155, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.19/1.28  tff(c_158, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_155])).
% 2.19/1.28  tff(c_161, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_129, c_158])).
% 2.19/1.28  tff(c_162, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_161])).
% 2.19/1.28  tff(c_12, plain, (![C_14, B_13, A_12]: (m1_subset_1(k1_funct_1(C_14, B_13), A_12) | ~r2_hidden(B_13, k1_relat_1(C_14)) | ~v1_funct_1(C_14) | ~v5_relat_1(C_14, A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.28  tff(c_166, plain, (![B_13, A_12]: (m1_subset_1(k1_funct_1('#skF_6', B_13), A_12) | ~r2_hidden(B_13, '#skF_3') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_12) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_12])).
% 2.19/1.28  tff(c_176, plain, (![B_103, A_104]: (m1_subset_1(k1_funct_1('#skF_6', B_103), A_104) | ~r2_hidden(B_103, '#skF_3') | ~v5_relat_1('#skF_6', A_104))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48, c_166])).
% 2.19/1.28  tff(c_66, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.28  tff(c_38, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.19/1.28  tff(c_74, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_66, c_38])).
% 2.19/1.28  tff(c_75, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_74])).
% 2.19/1.28  tff(c_211, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_176, c_75])).
% 2.19/1.28  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_42, c_211])).
% 2.19/1.28  tff(c_224, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 2.19/1.28  tff(c_55, plain, (![A_42]: (r2_hidden('#skF_2'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.19/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.28  tff(c_59, plain, (![A_42]: (~v1_xboole_0(A_42) | k1_xboole_0=A_42)), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.19/1.28  tff(c_228, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_224, c_59])).
% 2.19/1.28  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_228])).
% 2.19/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  Inference rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Ref     : 0
% 2.19/1.28  #Sup     : 38
% 2.19/1.28  #Fact    : 0
% 2.19/1.28  #Define  : 0
% 2.19/1.28  #Split   : 3
% 2.19/1.28  #Chain   : 0
% 2.19/1.28  #Close   : 0
% 2.19/1.28  
% 2.19/1.28  Ordering : KBO
% 2.19/1.28  
% 2.19/1.28  Simplification rules
% 2.19/1.28  ----------------------
% 2.19/1.28  #Subsume      : 0
% 2.19/1.28  #Demod        : 8
% 2.19/1.28  #Tautology    : 8
% 2.19/1.28  #SimpNegUnit  : 2
% 2.19/1.28  #BackRed      : 1
% 2.19/1.28  
% 2.19/1.28  #Partial instantiations: 0
% 2.19/1.28  #Strategies tried      : 1
% 2.19/1.28  
% 2.19/1.28  Timing (in seconds)
% 2.19/1.28  ----------------------
% 2.19/1.28  Preprocessing        : 0.34
% 2.19/1.28  Parsing              : 0.17
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.19
% 2.19/1.28  Inferencing          : 0.07
% 2.19/1.28  Reduction            : 0.06
% 2.19/1.28  Demodulation         : 0.04
% 2.19/1.28  BG Simplification    : 0.02
% 2.19/1.28  Subsumption          : 0.03
% 2.19/1.28  Abstraction          : 0.01
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.55
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
