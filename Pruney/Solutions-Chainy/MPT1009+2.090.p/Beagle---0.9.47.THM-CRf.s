%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 125 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 254 expanded)
%              Number of equality atoms :   35 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_85,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_89,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k9_relat_1(B_10,A_9),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_103,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_107,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_160,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_69,B_68,C_70) = A_69
      | ~ v1_funct_2(C_70,A_69,B_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_163,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_160])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_107,c_163])).

tff(c_167,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_166])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_187,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_4])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_273,plain,(
    ! [C_78,A_79,B_80] :
      ( k2_tarski(k1_funct_1(C_78,A_79),k1_funct_1(C_78,B_80)) = k9_relat_1(C_78,k2_tarski(A_79,B_80))
      | ~ r2_hidden(B_80,k1_relat_1(C_78))
      | ~ r2_hidden(A_79,k1_relat_1(C_78))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_287,plain,(
    ! [C_78,A_79] :
      ( k9_relat_1(C_78,k2_tarski(A_79,A_79)) = k1_tarski(k1_funct_1(C_78,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(C_78))
      | ~ r2_hidden(A_79,k1_relat_1(C_78))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_273])).

tff(c_292,plain,(
    ! [C_81,A_82] :
      ( k9_relat_1(C_81,k1_tarski(A_82)) = k1_tarski(k1_funct_1(C_81,A_82))
      | ~ r2_hidden(A_82,k1_relat_1(C_81))
      | ~ r2_hidden(A_82,k1_relat_1(C_81))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_294,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k1_tarski(k1_funct_1('#skF_6','#skF_3'))
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_187,c_292])).

tff(c_303,plain,(
    k9_relat_1('#skF_6',k1_relat_1('#skF_6')) = k1_tarski(k1_funct_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_50,c_187,c_167,c_294])).

tff(c_20,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_312,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_20])).

tff(c_321,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_312])).

tff(c_119,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k7_relset_1(A_53,B_54,C_55,D_56) = k9_relat_1(C_55,D_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_122,plain,(
    ! [D_56] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_56) = k9_relat_1('#skF_6',D_56) ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_42,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_123,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_42])).

tff(c_354,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_123])).

tff(c_401,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_354])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:13:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.26/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.26/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.32  
% 2.26/1.33  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.26/1.33  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.33  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.26/1.33  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.26/1.33  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.26/1.33  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.26/1.33  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.33  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 2.26/1.33  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.26/1.33  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.26/1.33  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.26/1.33  tff(c_85, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.33  tff(c_89, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_85])).
% 2.26/1.33  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k9_relat_1(B_10, A_9), k2_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.33  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.26/1.33  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.26/1.33  tff(c_48, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.26/1.33  tff(c_103, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.33  tff(c_107, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_103])).
% 2.26/1.33  tff(c_160, plain, (![B_68, A_69, C_70]: (k1_xboole_0=B_68 | k1_relset_1(A_69, B_68, C_70)=A_69 | ~v1_funct_2(C_70, A_69, B_68) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.26/1.33  tff(c_163, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_46, c_160])).
% 2.26/1.33  tff(c_166, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_107, c_163])).
% 2.26/1.33  tff(c_167, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_166])).
% 2.26/1.33  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.26/1.33  tff(c_187, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_4])).
% 2.26/1.33  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.26/1.33  tff(c_273, plain, (![C_78, A_79, B_80]: (k2_tarski(k1_funct_1(C_78, A_79), k1_funct_1(C_78, B_80))=k9_relat_1(C_78, k2_tarski(A_79, B_80)) | ~r2_hidden(B_80, k1_relat_1(C_78)) | ~r2_hidden(A_79, k1_relat_1(C_78)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.33  tff(c_287, plain, (![C_78, A_79]: (k9_relat_1(C_78, k2_tarski(A_79, A_79))=k1_tarski(k1_funct_1(C_78, A_79)) | ~r2_hidden(A_79, k1_relat_1(C_78)) | ~r2_hidden(A_79, k1_relat_1(C_78)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(superposition, [status(thm), theory('equality')], [c_14, c_273])).
% 2.26/1.33  tff(c_292, plain, (![C_81, A_82]: (k9_relat_1(C_81, k1_tarski(A_82))=k1_tarski(k1_funct_1(C_81, A_82)) | ~r2_hidden(A_82, k1_relat_1(C_81)) | ~r2_hidden(A_82, k1_relat_1(C_81)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_287])).
% 2.26/1.33  tff(c_294, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3')) | ~r2_hidden('#skF_3', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_187, c_292])).
% 2.26/1.33  tff(c_303, plain, (k9_relat_1('#skF_6', k1_relat_1('#skF_6'))=k1_tarski(k1_funct_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_50, c_187, c_167, c_294])).
% 2.26/1.33  tff(c_20, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.33  tff(c_312, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_303, c_20])).
% 2.26/1.33  tff(c_321, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_312])).
% 2.26/1.33  tff(c_119, plain, (![A_53, B_54, C_55, D_56]: (k7_relset_1(A_53, B_54, C_55, D_56)=k9_relat_1(C_55, D_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.26/1.33  tff(c_122, plain, (![D_56]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_56)=k9_relat_1('#skF_6', D_56))), inference(resolution, [status(thm)], [c_46, c_119])).
% 2.26/1.33  tff(c_42, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.26/1.33  tff(c_123, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_42])).
% 2.26/1.33  tff(c_354, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_123])).
% 2.26/1.33  tff(c_401, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_354])).
% 2.26/1.33  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_401])).
% 2.26/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  Inference rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Ref     : 0
% 2.26/1.33  #Sup     : 72
% 2.26/1.33  #Fact    : 2
% 2.26/1.33  #Define  : 0
% 2.26/1.33  #Split   : 0
% 2.26/1.33  #Chain   : 0
% 2.26/1.33  #Close   : 0
% 2.26/1.33  
% 2.26/1.33  Ordering : KBO
% 2.26/1.33  
% 2.26/1.33  Simplification rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Subsume      : 3
% 2.26/1.33  #Demod        : 49
% 2.26/1.33  #Tautology    : 43
% 2.26/1.33  #SimpNegUnit  : 3
% 2.26/1.33  #BackRed      : 7
% 2.26/1.33  
% 2.26/1.33  #Partial instantiations: 0
% 2.26/1.33  #Strategies tried      : 1
% 2.26/1.33  
% 2.26/1.33  Timing (in seconds)
% 2.26/1.33  ----------------------
% 2.26/1.34  Preprocessing        : 0.32
% 2.26/1.34  Parsing              : 0.16
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.25
% 2.26/1.34  Inferencing          : 0.10
% 2.26/1.34  Reduction            : 0.08
% 2.26/1.34  Demodulation         : 0.06
% 2.26/1.34  BG Simplification    : 0.02
% 2.26/1.34  Subsumption          : 0.05
% 2.26/1.34  Abstraction          : 0.01
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.34  Cooper               : 0.00
% 2.26/1.34  Total                : 0.60
% 2.26/1.34  Index Insertion      : 0.00
% 2.26/1.34  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
