%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 161 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  147 ( 357 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_63,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_18] : m1_subset_1('#skF_5'(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_97,plain,(
    ! [A_18] : r1_tarski('#skF_5'(A_18),A_18) ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_303,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(A_80,B_79)
      | ~ v1_zfmisc_1(B_79)
      | v1_xboole_0(B_79)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_831,plain,(
    ! [A_641] :
      ( '#skF_5'(A_641) = A_641
      | ~ v1_zfmisc_1(A_641)
      | v1_xboole_0(A_641)
      | v1_xboole_0('#skF_5'(A_641)) ) ),
    inference(resolution,[status(thm)],[c_97,c_303])).

tff(c_26,plain,(
    ! [A_18] : ~ v1_subset_1('#skF_5'(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_218,plain,(
    ! [B_69,A_70] :
      ( ~ v1_xboole_0(B_69)
      | v1_subset_1(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_224,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0('#skF_5'(A_18))
      | v1_subset_1('#skF_5'(A_18),A_18)
      | v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_28,c_218])).

tff(c_228,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0('#skF_5'(A_18))
      | v1_xboole_0(A_18) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_224])).

tff(c_864,plain,(
    ! [A_668] :
      ( '#skF_5'(A_668) = A_668
      | ~ v1_zfmisc_1(A_668)
      | v1_xboole_0(A_668) ) ),
    inference(resolution,[status(thm)],[c_831,c_228])).

tff(c_867,plain,
    ( '#skF_5'('#skF_6') = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_864])).

tff(c_870,plain,(
    '#skF_5'('#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_867])).

tff(c_886,plain,(
    ~ v1_subset_1('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_26])).

tff(c_44,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    ! [B_32,A_33] :
      ( ~ r2_hidden(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_99,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_10,B_46] :
      ( '#skF_2'(k1_tarski(A_10),B_46) = A_10
      | r1_tarski(k1_tarski(A_10),B_46) ) ),
    inference(resolution,[status(thm)],[c_99,c_12])).

tff(c_306,plain,(
    ! [A_10,B_46] :
      ( k1_tarski(A_10) = B_46
      | ~ v1_zfmisc_1(B_46)
      | v1_xboole_0(B_46)
      | v1_xboole_0(k1_tarski(A_10))
      | '#skF_2'(k1_tarski(A_10),B_46) = A_10 ) ),
    inference(resolution,[status(thm)],[c_107,c_303])).

tff(c_3315,plain,(
    ! [A_4018,B_4019] :
      ( k1_tarski(A_4018) = B_4019
      | ~ v1_zfmisc_1(B_4019)
      | v1_xboole_0(B_4019)
      | '#skF_2'(k1_tarski(A_4018),B_4019) = A_4018 ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_306])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1129,plain,(
    ! [A_865,B_866,B_867] :
      ( r2_hidden(A_865,B_866)
      | ~ r1_tarski(B_867,B_866)
      | v1_xboole_0(B_867)
      | ~ m1_subset_1(A_865,B_867) ) ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_1147,plain,(
    ! [A_880,A_881] :
      ( r2_hidden(A_880,A_881)
      | v1_xboole_0('#skF_5'(A_881))
      | ~ m1_subset_1(A_880,'#skF_5'(A_881)) ) ),
    inference(resolution,[status(thm)],[c_97,c_1129])).

tff(c_1150,plain,(
    ! [A_880] :
      ( r2_hidden(A_880,'#skF_6')
      | v1_xboole_0('#skF_5'('#skF_6'))
      | ~ m1_subset_1(A_880,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_1147])).

tff(c_1152,plain,(
    ! [A_880] :
      ( r2_hidden(A_880,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_880,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_1150])).

tff(c_1185,plain,(
    ! [A_908] :
      ( r2_hidden(A_908,'#skF_6')
      | ~ m1_subset_1(A_908,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1152])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1206,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_5,'#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1185,c_8])).

tff(c_3341,plain,(
    ! [A_4018] :
      ( r1_tarski(k1_tarski(A_4018),'#skF_6')
      | ~ m1_subset_1(A_4018,'#skF_6')
      | k1_tarski(A_4018) = '#skF_6'
      | ~ v1_zfmisc_1('#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3315,c_1206])).

tff(c_3434,plain,(
    ! [A_4018] :
      ( r1_tarski(k1_tarski(A_4018),'#skF_6')
      | ~ m1_subset_1(A_4018,'#skF_6')
      | k1_tarski(A_4018) = '#skF_6'
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3341])).

tff(c_3448,plain,(
    ! [A_4056] :
      ( r1_tarski(k1_tarski(A_4056),'#skF_6')
      | ~ m1_subset_1(A_4056,'#skF_6')
      | k1_tarski(A_4056) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3434])).

tff(c_38,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3457,plain,(
    ! [A_4056] :
      ( ~ v1_zfmisc_1('#skF_6')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(k1_tarski(A_4056))
      | ~ m1_subset_1(A_4056,'#skF_6')
      | k1_tarski(A_4056) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_3448,c_38])).

tff(c_3510,plain,(
    ! [A_4056] :
      ( v1_xboole_0('#skF_6')
      | v1_xboole_0(k1_tarski(A_4056))
      | ~ m1_subset_1(A_4056,'#skF_6')
      | k1_tarski(A_4056) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3457])).

tff(c_3516,plain,(
    ! [A_4093] :
      ( ~ m1_subset_1(A_4093,'#skF_6')
      | k1_tarski(A_4093) = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_46,c_3510])).

tff(c_3530,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_3516])).

tff(c_181,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_190,plain,
    ( k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_181])).

tff(c_195,plain,(
    k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_190])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_196,plain,(
    v1_subset_1(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_42])).

tff(c_3531,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3530,c_196])).

tff(c_3534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_3531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:53:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.81  
% 4.35/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.82  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 4.35/1.82  
% 4.35/1.82  %Foreground sorts:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Background operators:
% 4.35/1.82  
% 4.35/1.82  
% 4.35/1.82  %Foreground operators:
% 4.35/1.82  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.82  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.35/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.35/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.35/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.35/1.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.35/1.82  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.35/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.35/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.35/1.82  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.35/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.35/1.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.35/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.82  
% 4.35/1.84  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 4.35/1.84  tff(f_63, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.35/1.84  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.35/1.84  tff(f_93, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.35/1.84  tff(f_57, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 4.35/1.84  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.35/1.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.35/1.84  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.35/1.84  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.35/1.84  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.35/1.84  tff(c_46, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.35/1.84  tff(c_40, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.35/1.84  tff(c_28, plain, (![A_18]: (m1_subset_1('#skF_5'(A_18), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.35/1.84  tff(c_89, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.35/1.84  tff(c_97, plain, (![A_18]: (r1_tarski('#skF_5'(A_18), A_18))), inference(resolution, [status(thm)], [c_28, c_89])).
% 4.35/1.84  tff(c_303, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(A_80, B_79) | ~v1_zfmisc_1(B_79) | v1_xboole_0(B_79) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.84  tff(c_831, plain, (![A_641]: ('#skF_5'(A_641)=A_641 | ~v1_zfmisc_1(A_641) | v1_xboole_0(A_641) | v1_xboole_0('#skF_5'(A_641)))), inference(resolution, [status(thm)], [c_97, c_303])).
% 4.35/1.84  tff(c_26, plain, (![A_18]: (~v1_subset_1('#skF_5'(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.35/1.84  tff(c_218, plain, (![B_69, A_70]: (~v1_xboole_0(B_69) | v1_subset_1(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.35/1.84  tff(c_224, plain, (![A_18]: (~v1_xboole_0('#skF_5'(A_18)) | v1_subset_1('#skF_5'(A_18), A_18) | v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_28, c_218])).
% 4.35/1.84  tff(c_228, plain, (![A_18]: (~v1_xboole_0('#skF_5'(A_18)) | v1_xboole_0(A_18))), inference(negUnitSimplification, [status(thm)], [c_26, c_224])).
% 4.35/1.84  tff(c_864, plain, (![A_668]: ('#skF_5'(A_668)=A_668 | ~v1_zfmisc_1(A_668) | v1_xboole_0(A_668))), inference(resolution, [status(thm)], [c_831, c_228])).
% 4.35/1.84  tff(c_867, plain, ('#skF_5'('#skF_6')='#skF_6' | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_864])).
% 4.35/1.84  tff(c_870, plain, ('#skF_5'('#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_46, c_867])).
% 4.35/1.84  tff(c_886, plain, (~v1_subset_1('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_870, c_26])).
% 4.35/1.84  tff(c_44, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.35/1.84  tff(c_14, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.35/1.84  tff(c_49, plain, (![B_32, A_33]: (~r2_hidden(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.84  tff(c_53, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_14, c_49])).
% 4.35/1.84  tff(c_99, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.35/1.84  tff(c_12, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.35/1.84  tff(c_107, plain, (![A_10, B_46]: ('#skF_2'(k1_tarski(A_10), B_46)=A_10 | r1_tarski(k1_tarski(A_10), B_46))), inference(resolution, [status(thm)], [c_99, c_12])).
% 4.35/1.84  tff(c_306, plain, (![A_10, B_46]: (k1_tarski(A_10)=B_46 | ~v1_zfmisc_1(B_46) | v1_xboole_0(B_46) | v1_xboole_0(k1_tarski(A_10)) | '#skF_2'(k1_tarski(A_10), B_46)=A_10)), inference(resolution, [status(thm)], [c_107, c_303])).
% 4.35/1.84  tff(c_3315, plain, (![A_4018, B_4019]: (k1_tarski(A_4018)=B_4019 | ~v1_zfmisc_1(B_4019) | v1_xboole_0(B_4019) | '#skF_2'(k1_tarski(A_4018), B_4019)=A_4018)), inference(negUnitSimplification, [status(thm)], [c_53, c_306])).
% 4.35/1.84  tff(c_30, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.35/1.84  tff(c_135, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.35/1.84  tff(c_1129, plain, (![A_865, B_866, B_867]: (r2_hidden(A_865, B_866) | ~r1_tarski(B_867, B_866) | v1_xboole_0(B_867) | ~m1_subset_1(A_865, B_867))), inference(resolution, [status(thm)], [c_30, c_135])).
% 4.35/1.84  tff(c_1147, plain, (![A_880, A_881]: (r2_hidden(A_880, A_881) | v1_xboole_0('#skF_5'(A_881)) | ~m1_subset_1(A_880, '#skF_5'(A_881)))), inference(resolution, [status(thm)], [c_97, c_1129])).
% 4.35/1.84  tff(c_1150, plain, (![A_880]: (r2_hidden(A_880, '#skF_6') | v1_xboole_0('#skF_5'('#skF_6')) | ~m1_subset_1(A_880, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_870, c_1147])).
% 4.35/1.84  tff(c_1152, plain, (![A_880]: (r2_hidden(A_880, '#skF_6') | v1_xboole_0('#skF_6') | ~m1_subset_1(A_880, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_1150])).
% 4.35/1.84  tff(c_1185, plain, (![A_908]: (r2_hidden(A_908, '#skF_6') | ~m1_subset_1(A_908, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1152])).
% 4.35/1.84  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.35/1.84  tff(c_1206, plain, (![A_5]: (r1_tarski(A_5, '#skF_6') | ~m1_subset_1('#skF_2'(A_5, '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_1185, c_8])).
% 4.35/1.84  tff(c_3341, plain, (![A_4018]: (r1_tarski(k1_tarski(A_4018), '#skF_6') | ~m1_subset_1(A_4018, '#skF_6') | k1_tarski(A_4018)='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3315, c_1206])).
% 4.35/1.84  tff(c_3434, plain, (![A_4018]: (r1_tarski(k1_tarski(A_4018), '#skF_6') | ~m1_subset_1(A_4018, '#skF_6') | k1_tarski(A_4018)='#skF_6' | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3341])).
% 4.35/1.84  tff(c_3448, plain, (![A_4056]: (r1_tarski(k1_tarski(A_4056), '#skF_6') | ~m1_subset_1(A_4056, '#skF_6') | k1_tarski(A_4056)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_3434])).
% 4.35/1.84  tff(c_38, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.35/1.84  tff(c_3457, plain, (![A_4056]: (~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | v1_xboole_0(k1_tarski(A_4056)) | ~m1_subset_1(A_4056, '#skF_6') | k1_tarski(A_4056)='#skF_6')), inference(resolution, [status(thm)], [c_3448, c_38])).
% 4.35/1.84  tff(c_3510, plain, (![A_4056]: (v1_xboole_0('#skF_6') | v1_xboole_0(k1_tarski(A_4056)) | ~m1_subset_1(A_4056, '#skF_6') | k1_tarski(A_4056)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3457])).
% 4.35/1.84  tff(c_3516, plain, (![A_4093]: (~m1_subset_1(A_4093, '#skF_6') | k1_tarski(A_4093)='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_53, c_46, c_3510])).
% 4.35/1.84  tff(c_3530, plain, (k1_tarski('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_44, c_3516])).
% 4.35/1.84  tff(c_181, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.35/1.84  tff(c_190, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_181])).
% 4.35/1.84  tff(c_195, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_190])).
% 4.35/1.84  tff(c_42, plain, (v1_subset_1(k6_domain_1('#skF_6', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.35/1.84  tff(c_196, plain, (v1_subset_1(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_42])).
% 4.35/1.84  tff(c_3531, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3530, c_196])).
% 4.35/1.84  tff(c_3534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_886, c_3531])).
% 4.35/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.84  
% 4.35/1.84  Inference rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Ref     : 0
% 4.35/1.84  #Sup     : 512
% 4.35/1.84  #Fact    : 0
% 4.35/1.84  #Define  : 0
% 4.35/1.84  #Split   : 6
% 4.35/1.84  #Chain   : 0
% 4.35/1.84  #Close   : 0
% 4.35/1.84  
% 4.35/1.84  Ordering : KBO
% 4.35/1.84  
% 4.35/1.84  Simplification rules
% 4.35/1.84  ----------------------
% 4.35/1.84  #Subsume      : 142
% 4.35/1.84  #Demod        : 52
% 4.35/1.84  #Tautology    : 141
% 4.35/1.84  #SimpNegUnit  : 50
% 4.35/1.84  #BackRed      : 5
% 4.35/1.84  
% 4.35/1.84  #Partial instantiations: 2386
% 4.35/1.84  #Strategies tried      : 1
% 4.35/1.84  
% 4.35/1.84  Timing (in seconds)
% 4.35/1.84  ----------------------
% 4.35/1.85  Preprocessing        : 0.33
% 4.35/1.85  Parsing              : 0.18
% 4.35/1.85  CNF conversion       : 0.03
% 4.35/1.85  Main loop            : 0.70
% 4.35/1.85  Inferencing          : 0.34
% 4.35/1.85  Reduction            : 0.16
% 4.35/1.85  Demodulation         : 0.09
% 4.35/1.85  BG Simplification    : 0.03
% 4.35/1.85  Subsumption          : 0.12
% 4.35/1.85  Abstraction          : 0.03
% 4.35/1.85  MUC search           : 0.00
% 4.35/1.85  Cooper               : 0.00
% 4.35/1.85  Total                : 1.08
% 4.35/1.85  Index Insertion      : 0.00
% 4.35/1.85  Index Deletion       : 0.00
% 4.35/1.85  Index Matching       : 0.00
% 4.35/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
