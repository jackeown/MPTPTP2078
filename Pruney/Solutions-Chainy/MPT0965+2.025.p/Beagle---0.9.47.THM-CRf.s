%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:03 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   65 (  84 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 171 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_74,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_74])).

tff(c_84,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_80])).

tff(c_98,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_98])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_179,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_188,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_179])).

tff(c_644,plain,(
    ! [B_145,A_146,C_147] :
      ( k1_xboole_0 = B_145
      | k1_relset_1(A_146,B_145,C_147) = A_146
      | ~ v1_funct_2(C_147,A_146,B_145)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_659,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_644])).

tff(c_665,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_188,c_659])).

tff(c_666,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_665])).

tff(c_64,plain,(
    ! [C_36,A_37] :
      ( r2_hidden(C_36,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,(
    ! [C_36,A_37] :
      ( m1_subset_1(C_36,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(resolution,[status(thm)],[c_64,c_16])).

tff(c_343,plain,(
    ! [B_110,A_111] :
      ( r2_hidden(k1_funct_1(B_110,A_111),k2_relat_1(B_110))
      | ~ r2_hidden(A_111,k1_relat_1(B_110))
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1184,plain,(
    ! [B_179,A_180,A_181] :
      ( r2_hidden(k1_funct_1(B_179,A_180),A_181)
      | ~ m1_subset_1(k2_relat_1(B_179),k1_zfmisc_1(A_181))
      | ~ r2_hidden(A_180,k1_relat_1(B_179))
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(resolution,[status(thm)],[c_343,c_14])).

tff(c_1189,plain,(
    ! [B_182,A_183,A_184] :
      ( r2_hidden(k1_funct_1(B_182,A_183),A_184)
      | ~ r2_hidden(A_183,k1_relat_1(B_182))
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ r1_tarski(k2_relat_1(B_182),A_184) ) ),
    inference(resolution,[status(thm)],[c_72,c_1184])).

tff(c_46,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1201,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1189,c_46])).

tff(c_1207,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_50,c_666,c_1201])).

tff(c_1210,plain,
    ( ~ v5_relat_1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_1207])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_1210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.66  
% 3.45/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.45/1.67  
% 3.45/1.67  %Foreground sorts:
% 3.45/1.67  
% 3.45/1.67  
% 3.45/1.67  %Background operators:
% 3.45/1.67  
% 3.45/1.67  
% 3.45/1.67  %Foreground operators:
% 3.45/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.45/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.45/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.45/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.45/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.45/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.45/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.45/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.45/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.45/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.67  
% 3.54/1.68  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.54/1.68  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.54/1.68  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.54/1.68  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.54/1.68  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.54/1.68  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.54/1.68  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.54/1.68  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.54/1.68  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.54/1.68  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.54/1.68  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.54/1.68  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.68  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.68  tff(c_74, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.68  tff(c_80, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_74])).
% 3.54/1.68  tff(c_84, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_80])).
% 3.54/1.68  tff(c_98, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.54/1.68  tff(c_107, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_98])).
% 3.54/1.68  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.54/1.68  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.68  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.68  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.68  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.68  tff(c_179, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.54/1.68  tff(c_188, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_179])).
% 3.54/1.68  tff(c_644, plain, (![B_145, A_146, C_147]: (k1_xboole_0=B_145 | k1_relset_1(A_146, B_145, C_147)=A_146 | ~v1_funct_2(C_147, A_146, B_145) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.54/1.68  tff(c_659, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_644])).
% 3.54/1.68  tff(c_665, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_188, c_659])).
% 3.54/1.68  tff(c_666, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_48, c_665])).
% 3.54/1.68  tff(c_64, plain, (![C_36, A_37]: (r2_hidden(C_36, k1_zfmisc_1(A_37)) | ~r1_tarski(C_36, A_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.68  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.68  tff(c_72, plain, (![C_36, A_37]: (m1_subset_1(C_36, k1_zfmisc_1(A_37)) | ~r1_tarski(C_36, A_37))), inference(resolution, [status(thm)], [c_64, c_16])).
% 3.54/1.68  tff(c_343, plain, (![B_110, A_111]: (r2_hidden(k1_funct_1(B_110, A_111), k2_relat_1(B_110)) | ~r2_hidden(A_111, k1_relat_1(B_110)) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.54/1.68  tff(c_14, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.68  tff(c_1184, plain, (![B_179, A_180, A_181]: (r2_hidden(k1_funct_1(B_179, A_180), A_181) | ~m1_subset_1(k2_relat_1(B_179), k1_zfmisc_1(A_181)) | ~r2_hidden(A_180, k1_relat_1(B_179)) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179))), inference(resolution, [status(thm)], [c_343, c_14])).
% 3.54/1.68  tff(c_1189, plain, (![B_182, A_183, A_184]: (r2_hidden(k1_funct_1(B_182, A_183), A_184) | ~r2_hidden(A_183, k1_relat_1(B_182)) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~r1_tarski(k2_relat_1(B_182), A_184))), inference(resolution, [status(thm)], [c_72, c_1184])).
% 3.54/1.68  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.54/1.68  tff(c_1201, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_1189, c_46])).
% 3.54/1.68  tff(c_1207, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_50, c_666, c_1201])).
% 3.54/1.68  tff(c_1210, plain, (~v5_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_1207])).
% 3.54/1.68  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_1210])).
% 3.54/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.68  
% 3.54/1.68  Inference rules
% 3.54/1.68  ----------------------
% 3.54/1.68  #Ref     : 0
% 3.54/1.68  #Sup     : 230
% 3.54/1.68  #Fact    : 0
% 3.54/1.68  #Define  : 0
% 3.54/1.68  #Split   : 2
% 3.54/1.68  #Chain   : 0
% 3.54/1.68  #Close   : 0
% 3.54/1.68  
% 3.54/1.68  Ordering : KBO
% 3.54/1.68  
% 3.54/1.68  Simplification rules
% 3.54/1.68  ----------------------
% 3.54/1.68  #Subsume      : 3
% 3.54/1.68  #Demod        : 13
% 3.54/1.68  #Tautology    : 22
% 3.54/1.68  #SimpNegUnit  : 2
% 3.54/1.68  #BackRed      : 1
% 3.54/1.68  
% 3.54/1.68  #Partial instantiations: 0
% 3.54/1.68  #Strategies tried      : 1
% 3.54/1.68  
% 3.54/1.68  Timing (in seconds)
% 3.54/1.68  ----------------------
% 3.54/1.68  Preprocessing        : 0.31
% 3.54/1.68  Parsing              : 0.16
% 3.54/1.68  CNF conversion       : 0.02
% 3.54/1.68  Main loop            : 0.48
% 3.54/1.68  Inferencing          : 0.18
% 3.54/1.68  Reduction            : 0.12
% 3.54/1.68  Demodulation         : 0.08
% 3.54/1.68  BG Simplification    : 0.03
% 3.54/1.68  Subsumption          : 0.11
% 3.54/1.68  Abstraction          : 0.03
% 3.54/1.68  MUC search           : 0.00
% 3.54/1.68  Cooper               : 0.00
% 3.54/1.68  Total                : 0.82
% 3.54/1.68  Index Insertion      : 0.00
% 3.54/1.68  Index Deletion       : 0.00
% 3.54/1.68  Index Matching       : 0.00
% 3.54/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
