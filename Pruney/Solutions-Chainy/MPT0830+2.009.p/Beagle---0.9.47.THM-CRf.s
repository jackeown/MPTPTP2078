%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:27 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 115 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 194 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_243,plain,(
    ! [C_98,A_99,B_100] :
      ( m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ r1_tarski(k2_relat_1(C_98),B_100)
      | ~ r1_tarski(k1_relat_1(C_98),A_99)
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_159,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k5_relset_1(A_78,B_79,C_80,D_81) = k7_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_162,plain,(
    ! [D_81] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_81) = k7_relat_1('#skF_4',D_81) ),
    inference(resolution,[status(thm)],[c_34,c_159])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_163,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_32])).

tff(c_258,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_243,c_163])).

tff(c_277,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_280,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_280])).

tff(c_286,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_57,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_61,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_79,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(k7_relat_1(C_55,A_56),A_56)
      | ~ v4_relat_1(C_55,B_57)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_56] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_56),A_56)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_61,c_79])).

tff(c_87,plain,(
    ! [A_56] : v4_relat_1(k7_relat_1('#skF_4',A_56),A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_83])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_45,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_41])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_14,A_13)),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_64,A_65,B_66] :
      ( r1_tarski(A_64,A_65)
      | ~ r1_tarski(A_64,k2_relat_1(B_66))
      | ~ v5_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_110,plain,(
    ! [B_14,A_13,A_65] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_14,A_13)),A_65)
      | ~ v5_relat_1(B_14,A_65)
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_285,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_312,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_344,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_312])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45,c_344])).

tff(c_352,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_356,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_352])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_87,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.45  
% 2.71/1.45  %Foreground sorts:
% 2.71/1.45  
% 2.71/1.45  
% 2.71/1.45  %Background operators:
% 2.71/1.45  
% 2.71/1.45  
% 2.71/1.45  %Foreground operators:
% 2.71/1.45  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.71/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.71/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.71/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.45  
% 2.71/1.46  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.71/1.46  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.71/1.46  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.71/1.46  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.71/1.46  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.71/1.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.71/1.46  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.71/1.46  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.71/1.46  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 2.71/1.46  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.71/1.46  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.71/1.46  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.71/1.46  tff(c_36, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.46  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_36])).
% 2.71/1.46  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.71/1.46  tff(c_243, plain, (![C_98, A_99, B_100]: (m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~r1_tarski(k2_relat_1(C_98), B_100) | ~r1_tarski(k1_relat_1(C_98), A_99) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.71/1.46  tff(c_159, plain, (![A_78, B_79, C_80, D_81]: (k5_relset_1(A_78, B_79, C_80, D_81)=k7_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.71/1.46  tff(c_162, plain, (![D_81]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_81)=k7_relat_1('#skF_4', D_81))), inference(resolution, [status(thm)], [c_34, c_159])).
% 2.71/1.46  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.71/1.46  tff(c_163, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_32])).
% 2.71/1.46  tff(c_258, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_243, c_163])).
% 2.71/1.46  tff(c_277, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_258])).
% 2.71/1.46  tff(c_280, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_277])).
% 2.71/1.46  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_280])).
% 2.71/1.46  tff(c_286, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_258])).
% 2.71/1.46  tff(c_57, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.46  tff(c_61, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_57])).
% 2.71/1.46  tff(c_79, plain, (![C_55, A_56, B_57]: (v4_relat_1(k7_relat_1(C_55, A_56), A_56) | ~v4_relat_1(C_55, B_57) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.71/1.46  tff(c_83, plain, (![A_56]: (v4_relat_1(k7_relat_1('#skF_4', A_56), A_56) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_61, c_79])).
% 2.71/1.46  tff(c_87, plain, (![A_56]: (v4_relat_1(k7_relat_1('#skF_4', A_56), A_56))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_83])).
% 2.71/1.46  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.46  tff(c_41, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.46  tff(c_45, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_41])).
% 2.71/1.46  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(k7_relat_1(B_14, A_13)), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.71/1.46  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.46  tff(c_63, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.46  tff(c_100, plain, (![A_64, A_65, B_66]: (r1_tarski(A_64, A_65) | ~r1_tarski(A_64, k2_relat_1(B_66)) | ~v5_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_10, c_63])).
% 2.71/1.46  tff(c_110, plain, (![B_14, A_13, A_65]: (r1_tarski(k2_relat_1(k7_relat_1(B_14, A_13)), A_65) | ~v5_relat_1(B_14, A_65) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_100])).
% 2.71/1.46  tff(c_285, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_258])).
% 2.71/1.46  tff(c_312, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_285])).
% 2.71/1.46  tff(c_344, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_312])).
% 2.71/1.46  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_45, c_344])).
% 2.71/1.46  tff(c_352, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_285])).
% 2.71/1.46  tff(c_356, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_352])).
% 2.71/1.46  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_87, c_356])).
% 2.71/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  Inference rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Ref     : 0
% 2.71/1.46  #Sup     : 69
% 2.71/1.46  #Fact    : 0
% 2.71/1.46  #Define  : 0
% 2.71/1.46  #Split   : 3
% 2.71/1.46  #Chain   : 0
% 2.71/1.46  #Close   : 0
% 2.71/1.46  
% 2.71/1.46  Ordering : KBO
% 2.71/1.46  
% 2.71/1.46  Simplification rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Subsume      : 6
% 2.71/1.46  #Demod        : 13
% 2.71/1.46  #Tautology    : 5
% 2.71/1.46  #SimpNegUnit  : 0
% 2.71/1.46  #BackRed      : 1
% 2.71/1.46  
% 2.71/1.46  #Partial instantiations: 0
% 2.71/1.46  #Strategies tried      : 1
% 2.71/1.46  
% 2.71/1.46  Timing (in seconds)
% 2.71/1.46  ----------------------
% 2.71/1.47  Preprocessing        : 0.34
% 2.71/1.47  Parsing              : 0.18
% 2.71/1.47  CNF conversion       : 0.02
% 2.71/1.47  Main loop            : 0.27
% 2.71/1.47  Inferencing          : 0.10
% 2.71/1.47  Reduction            : 0.07
% 2.71/1.47  Demodulation         : 0.05
% 2.71/1.47  BG Simplification    : 0.02
% 2.71/1.47  Subsumption          : 0.06
% 2.71/1.47  Abstraction          : 0.02
% 2.71/1.47  MUC search           : 0.00
% 2.71/1.47  Cooper               : 0.00
% 2.71/1.47  Total                : 0.65
% 2.71/1.47  Index Insertion      : 0.00
% 2.71/1.47  Index Deletion       : 0.00
% 2.71/1.47  Index Matching       : 0.00
% 2.71/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
