%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:00 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :  101 ( 204 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_86,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(k1_funct_1(B_44,A_45),k2_relat_1(B_44))
      | ~ r2_hidden(A_45,k1_relat_1(B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_relset_1(A_35,B_36,C_37) = k2_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_69,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_59])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_69])).

tff(c_86,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_1'(A_54,B_55,C_56),B_55)
      | k1_relset_1(B_55,A_54,C_56) = B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(B_55,A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_89,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_6'),'#skF_3')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_86])).

tff(c_90,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_118,plain,(
    ! [D_70,A_71,B_72,C_73] :
      ( r2_hidden(k4_tarski(D_70,'#skF_2'(A_71,B_72,C_73,D_70)),C_73)
      | ~ r2_hidden(D_70,B_72)
      | k1_relset_1(B_72,A_71,C_73) != B_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(B_72,A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r2_hidden(A_8,k1_relat_1(C_10))
      | ~ r2_hidden(k4_tarski(A_8,B_9),C_10)
      | ~ v1_funct_1(C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_132,plain,(
    ! [D_74,C_75,B_76,A_77] :
      ( r2_hidden(D_74,k1_relat_1(C_75))
      | ~ v1_funct_1(C_75)
      | ~ v1_relat_1(C_75)
      | ~ r2_hidden(D_74,B_76)
      | k1_relset_1(B_76,A_77,C_75) != B_76
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(B_76,A_77))) ) ),
    inference(resolution,[status(thm)],[c_118,c_12])).

tff(c_145,plain,(
    ! [C_78,A_79] :
      ( r2_hidden('#skF_5',k1_relat_1(C_78))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | k1_relset_1('#skF_3',A_79,C_78) != '#skF_3'
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_79))) ) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_148,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_145])).

tff(c_151,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_52,c_44,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_151])).

tff(c_155,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_163,plain,(
    ! [B_83,A_84,C_85] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_84,B_83,C_85) = A_84
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_163])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_36,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.16/1.26  
% 2.16/1.26  %Foreground sorts:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Background operators:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Foreground operators:
% 2.16/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.16/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.16/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.16/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.16/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.26  
% 2.16/1.27  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.16/1.27  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.16/1.27  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.16/1.27  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.16/1.27  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.16/1.27  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.16/1.27  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.16/1.27  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.16/1.27  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.27  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.27  tff(c_46, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.27  tff(c_49, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_46])).
% 2.16/1.27  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_49])).
% 2.16/1.27  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.27  tff(c_66, plain, (![B_44, A_45]: (r2_hidden(k1_funct_1(B_44, A_45), k2_relat_1(B_44)) | ~r2_hidden(A_45, k1_relat_1(B_44)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.16/1.27  tff(c_54, plain, (![A_35, B_36, C_37]: (k2_relset_1(A_35, B_36, C_37)=k2_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.27  tff(c_58, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_54])).
% 2.16/1.27  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.27  tff(c_59, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34])).
% 2.16/1.27  tff(c_69, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_59])).
% 2.16/1.27  tff(c_72, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_69])).
% 2.16/1.27  tff(c_86, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_1'(A_54, B_55, C_56), B_55) | k1_relset_1(B_55, A_54, C_56)=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(B_55, A_54))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.16/1.27  tff(c_89, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_6'), '#skF_3') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_40, c_86])).
% 2.16/1.27  tff(c_90, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_89])).
% 2.16/1.27  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.27  tff(c_118, plain, (![D_70, A_71, B_72, C_73]: (r2_hidden(k4_tarski(D_70, '#skF_2'(A_71, B_72, C_73, D_70)), C_73) | ~r2_hidden(D_70, B_72) | k1_relset_1(B_72, A_71, C_73)!=B_72 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(B_72, A_71))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.16/1.27  tff(c_12, plain, (![A_8, C_10, B_9]: (r2_hidden(A_8, k1_relat_1(C_10)) | ~r2_hidden(k4_tarski(A_8, B_9), C_10) | ~v1_funct_1(C_10) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.27  tff(c_132, plain, (![D_74, C_75, B_76, A_77]: (r2_hidden(D_74, k1_relat_1(C_75)) | ~v1_funct_1(C_75) | ~v1_relat_1(C_75) | ~r2_hidden(D_74, B_76) | k1_relset_1(B_76, A_77, C_75)!=B_76 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(B_76, A_77))))), inference(resolution, [status(thm)], [c_118, c_12])).
% 2.16/1.27  tff(c_145, plain, (![C_78, A_79]: (r2_hidden('#skF_5', k1_relat_1(C_78)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | k1_relset_1('#skF_3', A_79, C_78)!='#skF_3' | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_79))))), inference(resolution, [status(thm)], [c_38, c_132])).
% 2.16/1.27  tff(c_148, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(resolution, [status(thm)], [c_40, c_145])).
% 2.16/1.27  tff(c_151, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_52, c_44, c_148])).
% 2.16/1.27  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_151])).
% 2.16/1.27  tff(c_155, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_89])).
% 2.16/1.27  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.27  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.27  tff(c_163, plain, (![B_83, A_84, C_85]: (k1_xboole_0=B_83 | k1_relset_1(A_84, B_83, C_85)=A_84 | ~v1_funct_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.16/1.27  tff(c_166, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_163])).
% 2.16/1.27  tff(c_169, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_166])).
% 2.16/1.27  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_36, c_169])).
% 2.16/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  Inference rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Ref     : 0
% 2.16/1.27  #Sup     : 23
% 2.16/1.27  #Fact    : 0
% 2.16/1.27  #Define  : 0
% 2.16/1.27  #Split   : 1
% 2.16/1.27  #Chain   : 0
% 2.16/1.27  #Close   : 0
% 2.16/1.27  
% 2.16/1.27  Ordering : KBO
% 2.16/1.27  
% 2.16/1.27  Simplification rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Subsume      : 1
% 2.16/1.27  #Demod        : 13
% 2.16/1.27  #Tautology    : 8
% 2.16/1.27  #SimpNegUnit  : 5
% 2.16/1.27  #BackRed      : 1
% 2.16/1.27  
% 2.16/1.27  #Partial instantiations: 0
% 2.16/1.27  #Strategies tried      : 1
% 2.16/1.27  
% 2.16/1.27  Timing (in seconds)
% 2.16/1.27  ----------------------
% 2.16/1.27  Preprocessing        : 0.32
% 2.16/1.27  Parsing              : 0.16
% 2.16/1.27  CNF conversion       : 0.02
% 2.16/1.27  Main loop            : 0.17
% 2.16/1.27  Inferencing          : 0.06
% 2.16/1.27  Reduction            : 0.05
% 2.16/1.27  Demodulation         : 0.04
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.03
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.28  Total                : 0.52
% 2.16/1.28  Index Insertion      : 0.00
% 2.16/1.28  Index Deletion       : 0.00
% 2.16/1.28  Index Matching       : 0.00
% 2.16/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
