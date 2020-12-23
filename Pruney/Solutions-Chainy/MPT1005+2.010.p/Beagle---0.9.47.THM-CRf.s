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
% DateTime   : Thu Dec  3 10:14:00 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 175 expanded)
%              Number of leaves         :   35 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 ( 269 expanded)
%              Number of equality atoms :   26 (  91 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_41,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_124,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_124])).

tff(c_133,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_138,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_58,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_60])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_138,c_24])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_215,plain,(
    ! [A_50] : m1_subset_1('#skF_4',k1_zfmisc_1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_30,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_226,plain,(
    ! [A_18] : v4_relat_1('#skF_4',A_18) ),
    inference(resolution,[status(thm)],[c_215,c_30])).

tff(c_231,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_234,plain,(
    ! [A_18] :
      ( k7_relat_1('#skF_4',A_18) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_226,c_231])).

tff(c_238,plain,(
    ! [A_54] : k7_relat_1('#skF_4',A_54) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_234])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_243,plain,(
    ! [A_54] :
      ( k9_relat_1('#skF_4',A_54) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_20])).

tff(c_248,plain,(
    ! [A_54] : k9_relat_1('#skF_4',A_54) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_152,c_243])).

tff(c_147,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_300,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k7_relset_1(A_67,B_68,C_69,D_70) = k9_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_303,plain,(
    ! [A_67,B_68,D_70] : k7_relset_1(A_67,B_68,'#skF_4',D_70) = k9_relat_1('#skF_4',D_70) ),
    inference(resolution,[status(thm)],[c_147,c_300])).

tff(c_309,plain,(
    ! [A_67,B_68,D_70] : k7_relset_1(A_67,B_68,'#skF_4',D_70) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_303])).

tff(c_34,plain,(
    k7_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_146,plain,(
    k7_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_138,c_34])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.22/1.32  
% 2.22/1.32  %Foreground sorts:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Background operators:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Foreground operators:
% 2.22/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.22/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.22/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.32  
% 2.22/1.33  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.22/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.33  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.22/1.33  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 2.22/1.33  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.22/1.33  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.22/1.33  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.22/1.33  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.22/1.33  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.33  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.22/1.33  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.22/1.33  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.22/1.33  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.22/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.22/1.33  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.22/1.33  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.33  tff(c_41, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 2.22/1.33  tff(c_124, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.33  tff(c_128, plain, (![A_42]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_124])).
% 2.22/1.33  tff(c_133, plain, (![A_43]: (~r2_hidden(A_43, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_128])).
% 2.22/1.33  tff(c_138, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.22/1.33  tff(c_58, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.33  tff(c_60, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 2.22/1.33  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_60])).
% 2.22/1.33  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.33  tff(c_152, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_138, c_24])).
% 2.22/1.33  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.33  tff(c_215, plain, (![A_50]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_12])).
% 2.22/1.33  tff(c_30, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.33  tff(c_226, plain, (![A_18]: (v4_relat_1('#skF_4', A_18))), inference(resolution, [status(thm)], [c_215, c_30])).
% 2.22/1.33  tff(c_231, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.33  tff(c_234, plain, (![A_18]: (k7_relat_1('#skF_4', A_18)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_226, c_231])).
% 2.22/1.33  tff(c_238, plain, (![A_54]: (k7_relat_1('#skF_4', A_54)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_234])).
% 2.22/1.33  tff(c_20, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.33  tff(c_243, plain, (![A_54]: (k9_relat_1('#skF_4', A_54)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_20])).
% 2.22/1.33  tff(c_248, plain, (![A_54]: (k9_relat_1('#skF_4', A_54)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_152, c_243])).
% 2.22/1.33  tff(c_147, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_12])).
% 2.22/1.33  tff(c_300, plain, (![A_67, B_68, C_69, D_70]: (k7_relset_1(A_67, B_68, C_69, D_70)=k9_relat_1(C_69, D_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.33  tff(c_303, plain, (![A_67, B_68, D_70]: (k7_relset_1(A_67, B_68, '#skF_4', D_70)=k9_relat_1('#skF_4', D_70))), inference(resolution, [status(thm)], [c_147, c_300])).
% 2.22/1.33  tff(c_309, plain, (![A_67, B_68, D_70]: (k7_relset_1(A_67, B_68, '#skF_4', D_70)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_303])).
% 2.22/1.33  tff(c_34, plain, (k7_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.22/1.33  tff(c_146, plain, (k7_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_138, c_34])).
% 2.22/1.33  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_309, c_146])).
% 2.22/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.33  
% 2.22/1.33  Inference rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Ref     : 0
% 2.22/1.33  #Sup     : 62
% 2.22/1.33  #Fact    : 0
% 2.22/1.33  #Define  : 0
% 2.22/1.33  #Split   : 0
% 2.22/1.33  #Chain   : 0
% 2.22/1.33  #Close   : 0
% 2.22/1.33  
% 2.22/1.33  Ordering : KBO
% 2.22/1.33  
% 2.22/1.33  Simplification rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Subsume      : 8
% 2.22/1.33  #Demod        : 43
% 2.22/1.33  #Tautology    : 43
% 2.22/1.33  #SimpNegUnit  : 0
% 2.22/1.33  #BackRed      : 16
% 2.22/1.33  
% 2.22/1.33  #Partial instantiations: 0
% 2.22/1.33  #Strategies tried      : 1
% 2.22/1.33  
% 2.22/1.33  Timing (in seconds)
% 2.22/1.33  ----------------------
% 2.22/1.33  Preprocessing        : 0.32
% 2.22/1.33  Parsing              : 0.18
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.19
% 2.22/1.33  Inferencing          : 0.07
% 2.22/1.33  Reduction            : 0.06
% 2.22/1.33  Demodulation         : 0.05
% 2.22/1.33  BG Simplification    : 0.01
% 2.22/1.33  Subsumption          : 0.02
% 2.22/1.33  Abstraction          : 0.01
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.34  Cooper               : 0.00
% 2.22/1.34  Total                : 0.54
% 2.22/1.34  Index Insertion      : 0.00
% 2.22/1.34  Index Deletion       : 0.00
% 2.22/1.34  Index Matching       : 0.00
% 2.22/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
