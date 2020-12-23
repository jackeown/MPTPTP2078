%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 816 expanded)
%              Number of leaves         :   45 ( 277 expanded)
%              Depth                    :   15
%              Number of atoms          :  358 (1684 expanded)
%              Number of equality atoms :   76 ( 193 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k8_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_98,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_10129,plain,(
    ! [A_729,B_730] :
      ( r2_hidden('#skF_2'(A_729,B_730),A_729)
      | r1_tarski(A_729,B_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10146,plain,(
    ! [A_729] : r1_tarski(A_729,A_729) ),
    inference(resolution,[status(thm)],[c_10129,c_8])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_4'(A_25,B_26),B_26)
      | k1_xboole_0 = B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,
    ( r2_hidden('#skF_9','#skF_8')
    | ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_72,plain,(
    ! [D_51] :
      ( r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8'))
      | r2_hidden('#skF_7',D_51)
      | ~ r2_hidden(D_51,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10122,plain,(
    ! [D_726] :
      ( r2_hidden('#skF_7',D_726)
      | ~ r2_hidden(D_726,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_72])).

tff(c_10126,plain,
    ( r2_hidden('#skF_7','#skF_1'('#skF_8'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_10122])).

tff(c_10127,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10126])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10605,plain,(
    ! [A_785,B_786,C_787] :
      ( k8_subset_1(A_785,B_786,C_787) = k3_xboole_0(B_786,C_787)
      | ~ m1_subset_1(B_786,k1_zfmisc_1(A_785)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10671,plain,(
    ! [C_790] : k8_subset_1(k1_zfmisc_1('#skF_6'),'#skF_8',C_790) = k3_xboole_0('#skF_8',C_790) ),
    inference(resolution,[status(thm)],[c_60,c_10605])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( ~ v1_xboole_0(B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10147,plain,(
    ! [A_729,B_730] :
      ( ~ v1_xboole_0(A_729)
      | r1_tarski(A_729,B_730) ) ),
    inference(resolution,[status(thm)],[c_10129,c_16])).

tff(c_48,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(A_39,k1_zfmisc_1(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10213,plain,(
    ! [A_745,B_746] :
      ( k8_subset_1(A_745,B_746,B_746) = B_746
      | ~ m1_subset_1(B_746,k1_zfmisc_1(A_745)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10326,plain,(
    ! [B_756,A_757] :
      ( k8_subset_1(B_756,A_757,A_757) = A_757
      | ~ r1_tarski(A_757,B_756) ) ),
    inference(resolution,[status(thm)],[c_48,c_10213])).

tff(c_10369,plain,(
    ! [B_759,A_760] :
      ( k8_subset_1(B_759,A_760,A_760) = A_760
      | ~ v1_xboole_0(A_760) ) ),
    inference(resolution,[status(thm)],[c_10147,c_10326])).

tff(c_10375,plain,(
    ! [B_759] : k8_subset_1(B_759,'#skF_8','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_10127,c_10369])).

tff(c_10678,plain,(
    k3_xboole_0('#skF_8','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_10671,c_10375])).

tff(c_10394,plain,(
    ! [A_762,B_763] :
      ( r2_hidden('#skF_3'(A_762,B_763),k3_xboole_0(A_762,B_763))
      | r1_xboole_0(A_762,B_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10405,plain,(
    ! [A_762,B_763] :
      ( ~ v1_xboole_0(k3_xboole_0(A_762,B_763))
      | r1_xboole_0(A_762,B_763) ) ),
    inference(resolution,[status(thm)],[c_10394,c_16])).

tff(c_10697,plain,
    ( ~ v1_xboole_0('#skF_8')
    | r1_xboole_0('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10678,c_10405])).

tff(c_10716,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10127,c_10697])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10712,plain,(
    ! [C_14] :
      ( ~ r1_xboole_0('#skF_8','#skF_8')
      | ~ r2_hidden(C_14,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10678,c_14])).

tff(c_10788,plain,(
    ! [C_794] : ~ r2_hidden(C_794,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10716,c_10712])).

tff(c_10809,plain,(
    ! [A_25] :
      ( k1_xboole_0 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_26,c_10788])).

tff(c_10835,plain,(
    ! [A_25] : ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_25)) ),
    inference(splitLeft,[status(thm)],[c_10809])).

tff(c_10837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10835,c_60])).

tff(c_10838,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10809])).

tff(c_38,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    ! [A_35] :
      ( k8_setfam_1(A_35,k1_xboole_0) = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_74,plain,(
    ! [A_35] : k8_setfam_1(A_35,k1_xboole_0) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_10850,plain,(
    ! [A_35] : k8_setfam_1(A_35,'#skF_8') = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10838,c_74])).

tff(c_58,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10173,plain,(
    ! [C_741,B_742,A_743] :
      ( r2_hidden(C_741,B_742)
      | ~ r2_hidden(C_741,A_743)
      | ~ r1_tarski(A_743,B_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10192,plain,(
    ! [B_744] :
      ( r2_hidden('#skF_7',B_744)
      | ~ r1_tarski('#skF_6',B_744) ) ),
    inference(resolution,[status(thm)],[c_58,c_10173])).

tff(c_10211,plain,(
    ~ r1_tarski('#skF_6',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_10192,c_105])).

tff(c_10886,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10850,c_10211])).

tff(c_10890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10146,c_10886])).

tff(c_10892,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_10126])).

tff(c_12613,plain,(
    ! [A_950,B_951,C_952] :
      ( k8_subset_1(A_950,B_951,C_952) = k3_xboole_0(B_951,C_952)
      | ~ m1_subset_1(B_951,k1_zfmisc_1(A_950)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12651,plain,(
    ! [C_953] : k8_subset_1(k1_zfmisc_1('#skF_6'),'#skF_8',C_953) = k3_xboole_0('#skF_8',C_953) ),
    inference(resolution,[status(thm)],[c_60,c_12613])).

tff(c_10929,plain,(
    ! [A_805,B_806] :
      ( k8_subset_1(A_805,B_806,B_806) = B_806
      | ~ m1_subset_1(B_806,k1_zfmisc_1(A_805)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10937,plain,(
    k8_subset_1(k1_zfmisc_1('#skF_6'),'#skF_8','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_10929])).

tff(c_12657,plain,(
    k3_xboole_0('#skF_8','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_12651,c_10937])).

tff(c_119,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [A_70,B_71] :
      ( ~ r1_xboole_0(A_70,B_71)
      | v1_xboole_0(k3_xboole_0(A_70,B_71)) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_12684,plain,
    ( ~ r1_xboole_0('#skF_8','#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12657,c_124])).

tff(c_12690,plain,(
    ~ r1_xboole_0('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_10892,c_12684])).

tff(c_11946,plain,(
    ! [A_905,B_906] :
      ( r2_hidden('#skF_4'(A_905,B_906),B_906)
      | k1_xboole_0 = B_906
      | ~ m1_subset_1(B_906,k1_zfmisc_1(A_905)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10121,plain,(
    ! [D_51] :
      ( r2_hidden('#skF_7',D_51)
      | ~ r2_hidden(D_51,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_72])).

tff(c_11982,plain,(
    ! [A_905] :
      ( r2_hidden('#skF_7','#skF_4'(A_905,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_905)) ) ),
    inference(resolution,[status(thm)],[c_11946,c_10121])).

tff(c_12932,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_11982])).

tff(c_11363,plain,(
    ! [A_861,B_862,C_863] :
      ( k8_subset_1(A_861,B_862,C_863) = k3_xboole_0(B_862,C_863)
      | ~ m1_subset_1(B_862,k1_zfmisc_1(A_861)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11380,plain,(
    ! [A_864,C_865] : k8_subset_1(A_864,k1_xboole_0,C_865) = k3_xboole_0(k1_xboole_0,C_865) ),
    inference(resolution,[status(thm)],[c_38,c_11363])).

tff(c_10938,plain,(
    ! [A_34] : k8_subset_1(A_34,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_10929])).

tff(c_11391,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11380,c_10938])).

tff(c_95,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_103,plain,(
    ! [A_34] : r1_tarski(k1_xboole_0,A_34) ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_11010,plain,(
    ! [C_820,B_821,A_822] :
      ( r2_hidden(C_820,B_821)
      | ~ r2_hidden(C_820,A_822)
      | ~ r1_tarski(A_822,B_821) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11153,plain,(
    ! [A_836,B_837] :
      ( r2_hidden('#skF_1'(A_836),B_837)
      | ~ r1_tarski(A_836,B_837)
      | v1_xboole_0(A_836) ) ),
    inference(resolution,[status(thm)],[c_4,c_11010])).

tff(c_11170,plain,(
    ! [B_838,A_839] :
      ( ~ v1_xboole_0(B_838)
      | ~ r1_tarski(A_839,B_838)
      | v1_xboole_0(A_839) ) ),
    inference(resolution,[status(thm)],[c_11153,c_16])).

tff(c_11201,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(A_34)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_103,c_11170])).

tff(c_11202,plain,(
    ! [A_34] : ~ v1_xboole_0(A_34) ),
    inference(splitLeft,[status(thm)],[c_11201])).

tff(c_11220,plain,(
    ! [A_70,B_71] : ~ r1_xboole_0(A_70,B_71) ),
    inference(negUnitSimplification,[status(thm)],[c_11202,c_124])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_11223,plain,(
    ! [A_10,B_11] : r2_hidden('#skF_3'(A_10,B_11),k3_xboole_0(A_10,B_11)) ),
    inference(negUnitSimplification,[status(thm)],[c_11220,c_12])).

tff(c_11407,plain,(
    r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11391,c_11223])).

tff(c_11261,plain,(
    ! [A_852,C_853,B_854] :
      ( m1_subset_1(A_852,C_853)
      | ~ m1_subset_1(B_854,k1_zfmisc_1(C_853))
      | ~ r2_hidden(A_852,B_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_11270,plain,(
    ! [A_852,A_34] :
      ( m1_subset_1(A_852,A_34)
      | ~ r2_hidden(A_852,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_11261])).

tff(c_11475,plain,(
    ! [A_869] : m1_subset_1('#skF_3'(k1_xboole_0,k1_xboole_0),A_869) ),
    inference(resolution,[status(thm)],[c_11407,c_11270])).

tff(c_46,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11497,plain,(
    ! [B_40] : r1_tarski('#skF_3'(k1_xboole_0,k1_xboole_0),B_40) ),
    inference(resolution,[status(thm)],[c_11475,c_46])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11460,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0),B_6)
      | ~ r1_tarski(k1_xboole_0,B_6) ) ),
    inference(resolution,[status(thm)],[c_11407,c_6])).

tff(c_11505,plain,(
    ! [B_870] : r2_hidden('#skF_3'(k1_xboole_0,k1_xboole_0),B_870) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_11460])).

tff(c_11523,plain,(
    r2_hidden('#skF_7','#skF_3'(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_11505,c_10121])).

tff(c_11530,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_7',B_6)
      | ~ r1_tarski('#skF_3'(k1_xboole_0,k1_xboole_0),B_6) ) ),
    inference(resolution,[status(thm)],[c_11523,c_6])).

tff(c_11533,plain,(
    ! [B_6] : r2_hidden('#skF_7',B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11497,c_11530])).

tff(c_11570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11533,c_105])).

tff(c_11571,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11201])).

tff(c_12734,plain,(
    ! [A_957,C_958] : k8_subset_1(A_957,k1_xboole_0,C_958) = k3_xboole_0(k1_xboole_0,C_958) ),
    inference(resolution,[status(thm)],[c_38,c_12613])).

tff(c_12745,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12734,c_10938])).

tff(c_11110,plain,(
    ! [A_827,B_828] :
      ( r2_hidden('#skF_3'(A_827,B_828),k3_xboole_0(A_827,B_828))
      | r1_xboole_0(A_827,B_828) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_11121,plain,(
    ! [A_827,B_828] :
      ( ~ v1_xboole_0(k3_xboole_0(A_827,B_828))
      | r1_xboole_0(A_827,B_828) ) ),
    inference(resolution,[status(thm)],[c_11110,c_16])).

tff(c_12767,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12745,c_11121])).

tff(c_12783,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11571,c_12767])).

tff(c_12937,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12932,c_12932,c_12783])).

tff(c_12959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12690,c_12937])).

tff(c_12961,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11982])).

tff(c_11733,plain,(
    ! [A_885,B_886] :
      ( k6_setfam_1(A_885,B_886) = k1_setfam_1(B_886)
      | ~ m1_subset_1(B_886,k1_zfmisc_1(k1_zfmisc_1(A_885))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11746,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_11733])).

tff(c_13008,plain,(
    ! [A_965,B_966] :
      ( k8_setfam_1(A_965,B_966) = k6_setfam_1(A_965,B_966)
      | k1_xboole_0 = B_966
      | ~ m1_subset_1(B_966,k1_zfmisc_1(k1_zfmisc_1(A_965))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_13031,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_13008])).

tff(c_13042,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11746,c_13031])).

tff(c_13043,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_12961,c_13042])).

tff(c_13088,plain,(
    ~ r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13043,c_105])).

tff(c_12358,plain,(
    ! [A_934,B_935] :
      ( r2_hidden('#skF_5'(A_934,B_935),A_934)
      | r1_tarski(B_935,k1_setfam_1(A_934))
      | k1_xboole_0 = A_934 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12399,plain,(
    ! [B_935] :
      ( r2_hidden('#skF_7','#skF_5'('#skF_8',B_935))
      | r1_tarski(B_935,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_12358,c_10121])).

tff(c_13405,plain,(
    ! [B_935] :
      ( r2_hidden('#skF_7','#skF_5'('#skF_8',B_935))
      | r1_tarski(B_935,k1_setfam_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12961,c_12399])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_tarski(A_17),B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11840,plain,(
    ! [B_895,A_896] :
      ( ~ r1_tarski(B_895,'#skF_5'(A_896,B_895))
      | r1_tarski(B_895,k1_setfam_1(A_896))
      | k1_xboole_0 = A_896 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14790,plain,(
    ! [A_1036,A_1037] :
      ( r1_tarski(k1_tarski(A_1036),k1_setfam_1(A_1037))
      | k1_xboole_0 = A_1037
      | ~ r2_hidden(A_1036,'#skF_5'(A_1037,k1_tarski(A_1036))) ) ),
    inference(resolution,[status(thm)],[c_20,c_11840])).

tff(c_14802,plain,
    ( k1_xboole_0 = '#skF_8'
    | r1_tarski(k1_tarski('#skF_7'),k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_13405,c_14790])).

tff(c_14819,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_setfam_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_12961,c_14802])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14845,plain,(
    r2_hidden('#skF_7',k1_setfam_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_14819,c_18])).

tff(c_14864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13088,c_14845])).

tff(c_14866,plain,(
    r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_14871,plain,(
    ~ r2_hidden('#skF_7',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_14877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14866,c_14871])).

tff(c_14878,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14922,plain,(
    ! [A_1057,B_1058] :
      ( ~ r2_hidden('#skF_2'(A_1057,B_1058),B_1058)
      | r1_tarski(A_1057,B_1058) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14927,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_14922])).

tff(c_14865,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_15010,plain,(
    ! [C_1073,B_1074,A_1075] :
      ( r2_hidden(C_1073,B_1074)
      | ~ r2_hidden(C_1073,A_1075)
      | ~ r1_tarski(A_1075,B_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15026,plain,(
    ! [B_1074] :
      ( r2_hidden('#skF_9',B_1074)
      | ~ r1_tarski('#skF_8',B_1074) ) ),
    inference(resolution,[status(thm)],[c_14865,c_15010])).

tff(c_50,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k1_setfam_1(B_42),A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16470,plain,(
    ! [A_1176,B_1177,C_1178] :
      ( k8_subset_1(A_1176,B_1177,C_1178) = k3_xboole_0(B_1177,C_1178)
      | ~ m1_subset_1(B_1177,k1_zfmisc_1(A_1176)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16502,plain,(
    ! [C_1180] : k8_subset_1(k1_zfmisc_1('#skF_6'),'#skF_8',C_1180) = k3_xboole_0('#skF_8',C_1180) ),
    inference(resolution,[status(thm)],[c_60,c_16470])).

tff(c_14941,plain,(
    ! [A_1065,B_1066] :
      ( k8_subset_1(A_1065,B_1066,B_1066) = B_1066
      | ~ m1_subset_1(B_1066,k1_zfmisc_1(A_1065)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14949,plain,(
    k8_subset_1(k1_zfmisc_1('#skF_6'),'#skF_8','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_14941])).

tff(c_16508,plain,(
    k3_xboole_0('#skF_8','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_16502,c_14949])).

tff(c_15029,plain,(
    ! [B_1076] :
      ( r2_hidden('#skF_9',B_1076)
      | ~ r1_tarski('#skF_8',B_1076) ) ),
    inference(resolution,[status(thm)],[c_14865,c_15010])).

tff(c_15040,plain,(
    ! [A_10,B_11] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r1_tarski('#skF_8',k3_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_15029,c_14])).

tff(c_16523,plain,
    ( ~ r1_xboole_0('#skF_8','#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_16508,c_15040])).

tff(c_16542,plain,(
    ~ r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14927,c_16523])).

tff(c_15141,plain,(
    ! [A_1091,B_1092] :
      ( k6_setfam_1(A_1091,B_1092) = k1_setfam_1(B_1092)
      | ~ m1_subset_1(B_1092,k1_zfmisc_1(k1_zfmisc_1(A_1091))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_15154,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_15141])).

tff(c_17292,plain,(
    ! [A_1218,B_1219] :
      ( k8_setfam_1(A_1218,B_1219) = k6_setfam_1(A_1218,B_1219)
      | k1_xboole_0 = B_1219
      | ~ m1_subset_1(B_1219,k1_zfmisc_1(k1_zfmisc_1(A_1218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_17303,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60,c_17292])).

tff(c_17311,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15154,c_17303])).

tff(c_17315,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17311])).

tff(c_15979,plain,(
    ! [A_1155,B_1156] :
      ( k1_subset_1(A_1155) = B_1156
      | ~ r1_tarski(B_1156,k3_subset_1(A_1155,B_1156))
      | ~ m1_subset_1(B_1156,k1_zfmisc_1(A_1155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16010,plain,(
    ! [A_1155] :
      ( k1_subset_1(A_1155) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1155)) ) ),
    inference(resolution,[status(thm)],[c_103,c_15979])).

tff(c_16027,plain,(
    ! [A_1155] : k1_subset_1(A_1155) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16010])).

tff(c_15128,plain,(
    ! [A_1089,B_1090] :
      ( r2_hidden('#skF_1'(A_1089),B_1090)
      | ~ r1_tarski(A_1089,B_1090)
      | v1_xboole_0(A_1089) ) ),
    inference(resolution,[status(thm)],[c_4,c_15010])).

tff(c_15167,plain,(
    ! [B_1094,A_1095] :
      ( ~ v1_xboole_0(B_1094)
      | ~ r1_tarski(A_1095,B_1094)
      | v1_xboole_0(A_1095) ) ),
    inference(resolution,[status(thm)],[c_15128,c_16])).

tff(c_15197,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(A_34)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_103,c_15167])).

tff(c_15220,plain,(
    ! [A_34] : ~ v1_xboole_0(A_34) ),
    inference(splitLeft,[status(thm)],[c_15197])).

tff(c_15224,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_15220,c_4])).

tff(c_15297,plain,(
    ! [A_1111,C_1112,B_1113] :
      ( m1_subset_1(A_1111,C_1112)
      | ~ m1_subset_1(B_1113,k1_zfmisc_1(C_1112))
      | ~ r2_hidden(A_1111,B_1113) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_15310,plain,(
    ! [A_1114,A_1115] :
      ( m1_subset_1(A_1114,A_1115)
      | ~ r2_hidden(A_1114,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_15297])).

tff(c_15327,plain,(
    ! [A_1115] : m1_subset_1('#skF_1'(k1_xboole_0),A_1115) ),
    inference(resolution,[status(thm)],[c_15224,c_15310])).

tff(c_15332,plain,(
    ! [A_1116] : m1_subset_1('#skF_1'(k1_xboole_0),A_1116) ),
    inference(resolution,[status(thm)],[c_15224,c_15310])).

tff(c_15350,plain,(
    ! [B_40] : r1_tarski('#skF_1'(k1_xboole_0),B_40) ),
    inference(resolution,[status(thm)],[c_15332,c_46])).

tff(c_15998,plain,(
    ! [A_1155] :
      ( k1_subset_1(A_1155) = '#skF_1'(k1_xboole_0)
      | ~ m1_subset_1('#skF_1'(k1_xboole_0),k1_zfmisc_1(A_1155)) ) ),
    inference(resolution,[status(thm)],[c_15350,c_15979])).

tff(c_16022,plain,(
    ! [A_1155] : k1_subset_1(A_1155) = '#skF_1'(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15327,c_15998])).

tff(c_16039,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16027,c_16022])).

tff(c_52,plain,(
    ! [A_43,C_45,B_44] :
      ( m1_subset_1(A_43,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_15528,plain,(
    ! [A_1128,C_1129] :
      ( m1_subset_1(A_1128,C_1129)
      | ~ r2_hidden(A_1128,'#skF_1'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_15332,c_52])).

tff(c_15551,plain,(
    ! [C_1129] : m1_subset_1('#skF_1'('#skF_1'(k1_xboole_0)),C_1129) ),
    inference(resolution,[status(thm)],[c_15224,c_15528])).

tff(c_16043,plain,(
    ! [C_1129] : m1_subset_1(k1_xboole_0,C_1129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16039,c_16039,c_15551])).

tff(c_14898,plain,(
    ! [A_1046,B_1047,C_1048] :
      ( ~ r1_xboole_0(A_1046,B_1047)
      | ~ r2_hidden(C_1048,k3_xboole_0(A_1046,B_1047)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14903,plain,(
    ! [A_1046,B_1047] :
      ( ~ r1_xboole_0(A_1046,B_1047)
      | v1_xboole_0(k3_xboole_0(A_1046,B_1047)) ) ),
    inference(resolution,[status(thm)],[c_4,c_14898])).

tff(c_15223,plain,(
    ! [A_1046,B_1047] : ~ r1_xboole_0(A_1046,B_1047) ),
    inference(negUnitSimplification,[status(thm)],[c_15220,c_14903])).

tff(c_34,plain,(
    ! [B_31,C_33,A_30] :
      ( r1_xboole_0(B_31,C_33)
      | ~ r1_tarski(B_31,k3_subset_1(A_30,C_33))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16294,plain,(
    ! [B_1164,A_1165,C_1166] :
      ( ~ r1_tarski(B_1164,k3_subset_1(A_1165,C_1166))
      | ~ m1_subset_1(C_1166,k1_zfmisc_1(A_1165))
      | ~ m1_subset_1(B_1164,k1_zfmisc_1(A_1165)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15223,c_34])).

tff(c_16314,plain,(
    ! [C_1166,A_1165] :
      ( ~ m1_subset_1(C_1166,k1_zfmisc_1(A_1165))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1165)) ) ),
    inference(resolution,[status(thm)],[c_103,c_16294])).

tff(c_16321,plain,(
    ! [C_1166,A_1165] : ~ m1_subset_1(C_1166,k1_zfmisc_1(A_1165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16043,c_16314])).

tff(c_16325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16321,c_60])).

tff(c_16326,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_15197])).

tff(c_16572,plain,(
    ! [A_1183,C_1184] : k8_subset_1(A_1183,k1_xboole_0,C_1184) = k3_xboole_0(k1_xboole_0,C_1184) ),
    inference(resolution,[status(thm)],[c_38,c_16470])).

tff(c_14950,plain,(
    ! [A_34] : k8_subset_1(A_34,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_14941])).

tff(c_16583,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16572,c_14950])).

tff(c_15057,plain,(
    ! [A_1078,B_1079] :
      ( r2_hidden('#skF_3'(A_1078,B_1079),k3_xboole_0(A_1078,B_1079))
      | r1_xboole_0(A_1078,B_1079) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_15068,plain,(
    ! [A_1078,B_1079] :
      ( ~ v1_xboole_0(k3_xboole_0(A_1078,B_1079))
      | r1_xboole_0(A_1078,B_1079) ) ),
    inference(resolution,[status(thm)],[c_15057,c_16])).

tff(c_16605,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16583,c_15068])).

tff(c_16621,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16326,c_16605])).

tff(c_17329,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17315,c_17315,c_16621])).

tff(c_17342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16542,c_17329])).

tff(c_17343,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_17311])).

tff(c_15025,plain,(
    ! [B_1074] :
      ( r2_hidden('#skF_7',B_1074)
      | ~ r1_tarski(k8_setfam_1('#skF_6','#skF_8'),B_1074) ) ),
    inference(resolution,[status(thm)],[c_14866,c_15010])).

tff(c_17445,plain,(
    ! [B_1225] :
      ( r2_hidden('#skF_7',B_1225)
      | ~ r1_tarski(k1_setfam_1('#skF_8'),B_1225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17343,c_15025])).

tff(c_17467,plain,(
    ! [A_1226] :
      ( r2_hidden('#skF_7',A_1226)
      | ~ r2_hidden(A_1226,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_50,c_17445])).

tff(c_17487,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_15026,c_17467])).

tff(c_17510,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14927,c_17487])).

tff(c_17512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14878,c_17510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:33:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.55/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.27  
% 8.74/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 8.74/3.28  
% 8.74/3.28  %Foreground sorts:
% 8.74/3.28  
% 8.74/3.28  
% 8.74/3.28  %Background operators:
% 8.74/3.28  
% 8.74/3.28  
% 8.74/3.28  %Foreground operators:
% 8.74/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.74/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.74/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.74/3.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.74/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.74/3.28  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 8.74/3.28  tff('#skF_7', type, '#skF_7': $i).
% 8.74/3.28  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 8.74/3.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.74/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.74/3.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.74/3.28  tff('#skF_6', type, '#skF_6': $i).
% 8.74/3.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.74/3.28  tff('#skF_9', type, '#skF_9': $i).
% 8.74/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.74/3.28  tff('#skF_8', type, '#skF_8': $i).
% 8.74/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.74/3.28  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 8.74/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.74/3.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.74/3.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.74/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.74/3.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.74/3.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.74/3.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.74/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.74/3.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.74/3.28  
% 8.74/3.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.74/3.31  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 8.74/3.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.74/3.31  tff(f_148, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 8.74/3.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 8.74/3.31  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 8.74/3.31  tff(f_117, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.74/3.31  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k8_subset_1)).
% 8.74/3.31  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.74/3.31  tff(f_98, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.74/3.31  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 8.74/3.31  tff(f_127, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.74/3.31  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 8.74/3.31  tff(f_136, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 8.74/3.31  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.74/3.31  tff(f_121, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 8.74/3.31  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 8.74/3.31  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 8.74/3.31  tff(c_10129, plain, (![A_729, B_730]: (r2_hidden('#skF_2'(A_729, B_730), A_729) | r1_tarski(A_729, B_730))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_10146, plain, (![A_729]: (r1_tarski(A_729, A_729))), inference(resolution, [status(thm)], [c_10129, c_8])).
% 8.74/3.31  tff(c_26, plain, (![A_25, B_26]: (r2_hidden('#skF_4'(A_25, B_26), B_26) | k1_xboole_0=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.74/3.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.74/3.31  tff(c_64, plain, (r2_hidden('#skF_9', '#skF_8') | ~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.74/3.31  tff(c_105, plain, (~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_64])).
% 8.74/3.31  tff(c_72, plain, (![D_51]: (r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8')) | r2_hidden('#skF_7', D_51) | ~r2_hidden(D_51, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.74/3.31  tff(c_10122, plain, (![D_726]: (r2_hidden('#skF_7', D_726) | ~r2_hidden(D_726, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_105, c_72])).
% 8.74/3.31  tff(c_10126, plain, (r2_hidden('#skF_7', '#skF_1'('#skF_8')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_10122])).
% 8.74/3.31  tff(c_10127, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_10126])).
% 8.74/3.31  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.74/3.31  tff(c_10605, plain, (![A_785, B_786, C_787]: (k8_subset_1(A_785, B_786, C_787)=k3_xboole_0(B_786, C_787) | ~m1_subset_1(B_786, k1_zfmisc_1(A_785)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.74/3.31  tff(c_10671, plain, (![C_790]: (k8_subset_1(k1_zfmisc_1('#skF_6'), '#skF_8', C_790)=k3_xboole_0('#skF_8', C_790))), inference(resolution, [status(thm)], [c_60, c_10605])).
% 8.74/3.31  tff(c_16, plain, (![B_16, A_15]: (~v1_xboole_0(B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.74/3.31  tff(c_10147, plain, (![A_729, B_730]: (~v1_xboole_0(A_729) | r1_tarski(A_729, B_730))), inference(resolution, [status(thm)], [c_10129, c_16])).
% 8.74/3.31  tff(c_48, plain, (![A_39, B_40]: (m1_subset_1(A_39, k1_zfmisc_1(B_40)) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.74/3.31  tff(c_10213, plain, (![A_745, B_746]: (k8_subset_1(A_745, B_746, B_746)=B_746 | ~m1_subset_1(B_746, k1_zfmisc_1(A_745)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.74/3.31  tff(c_10326, plain, (![B_756, A_757]: (k8_subset_1(B_756, A_757, A_757)=A_757 | ~r1_tarski(A_757, B_756))), inference(resolution, [status(thm)], [c_48, c_10213])).
% 8.74/3.31  tff(c_10369, plain, (![B_759, A_760]: (k8_subset_1(B_759, A_760, A_760)=A_760 | ~v1_xboole_0(A_760))), inference(resolution, [status(thm)], [c_10147, c_10326])).
% 8.74/3.31  tff(c_10375, plain, (![B_759]: (k8_subset_1(B_759, '#skF_8', '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_10127, c_10369])).
% 8.74/3.31  tff(c_10678, plain, (k3_xboole_0('#skF_8', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_10671, c_10375])).
% 8.74/3.31  tff(c_10394, plain, (![A_762, B_763]: (r2_hidden('#skF_3'(A_762, B_763), k3_xboole_0(A_762, B_763)) | r1_xboole_0(A_762, B_763))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_10405, plain, (![A_762, B_763]: (~v1_xboole_0(k3_xboole_0(A_762, B_763)) | r1_xboole_0(A_762, B_763))), inference(resolution, [status(thm)], [c_10394, c_16])).
% 8.74/3.31  tff(c_10697, plain, (~v1_xboole_0('#skF_8') | r1_xboole_0('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10678, c_10405])).
% 8.74/3.31  tff(c_10716, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10127, c_10697])).
% 8.74/3.31  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_10712, plain, (![C_14]: (~r1_xboole_0('#skF_8', '#skF_8') | ~r2_hidden(C_14, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10678, c_14])).
% 8.74/3.31  tff(c_10788, plain, (![C_794]: (~r2_hidden(C_794, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10716, c_10712])).
% 8.74/3.31  tff(c_10809, plain, (![A_25]: (k1_xboole_0='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_26, c_10788])).
% 8.74/3.31  tff(c_10835, plain, (![A_25]: (~m1_subset_1('#skF_8', k1_zfmisc_1(A_25)))), inference(splitLeft, [status(thm)], [c_10809])).
% 8.74/3.31  tff(c_10837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10835, c_60])).
% 8.74/3.31  tff(c_10838, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_10809])).
% 8.74/3.31  tff(c_38, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.74/3.31  tff(c_40, plain, (![A_35]: (k8_setfam_1(A_35, k1_xboole_0)=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.74/3.31  tff(c_74, plain, (![A_35]: (k8_setfam_1(A_35, k1_xboole_0)=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 8.74/3.31  tff(c_10850, plain, (![A_35]: (k8_setfam_1(A_35, '#skF_8')=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_10838, c_74])).
% 8.74/3.31  tff(c_58, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.74/3.31  tff(c_10173, plain, (![C_741, B_742, A_743]: (r2_hidden(C_741, B_742) | ~r2_hidden(C_741, A_743) | ~r1_tarski(A_743, B_742))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_10192, plain, (![B_744]: (r2_hidden('#skF_7', B_744) | ~r1_tarski('#skF_6', B_744))), inference(resolution, [status(thm)], [c_58, c_10173])).
% 8.74/3.31  tff(c_10211, plain, (~r1_tarski('#skF_6', k8_setfam_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_10192, c_105])).
% 8.74/3.31  tff(c_10886, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10850, c_10211])).
% 8.74/3.31  tff(c_10890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10146, c_10886])).
% 8.74/3.31  tff(c_10892, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_10126])).
% 8.74/3.31  tff(c_12613, plain, (![A_950, B_951, C_952]: (k8_subset_1(A_950, B_951, C_952)=k3_xboole_0(B_951, C_952) | ~m1_subset_1(B_951, k1_zfmisc_1(A_950)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.74/3.31  tff(c_12651, plain, (![C_953]: (k8_subset_1(k1_zfmisc_1('#skF_6'), '#skF_8', C_953)=k3_xboole_0('#skF_8', C_953))), inference(resolution, [status(thm)], [c_60, c_12613])).
% 8.74/3.31  tff(c_10929, plain, (![A_805, B_806]: (k8_subset_1(A_805, B_806, B_806)=B_806 | ~m1_subset_1(B_806, k1_zfmisc_1(A_805)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.74/3.31  tff(c_10937, plain, (k8_subset_1(k1_zfmisc_1('#skF_6'), '#skF_8', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_60, c_10929])).
% 8.74/3.31  tff(c_12657, plain, (k3_xboole_0('#skF_8', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_12651, c_10937])).
% 8.74/3.31  tff(c_119, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_124, plain, (![A_70, B_71]: (~r1_xboole_0(A_70, B_71) | v1_xboole_0(k3_xboole_0(A_70, B_71)))), inference(resolution, [status(thm)], [c_4, c_119])).
% 8.74/3.31  tff(c_12684, plain, (~r1_xboole_0('#skF_8', '#skF_8') | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_12657, c_124])).
% 8.74/3.31  tff(c_12690, plain, (~r1_xboole_0('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10892, c_12684])).
% 8.74/3.31  tff(c_11946, plain, (![A_905, B_906]: (r2_hidden('#skF_4'(A_905, B_906), B_906) | k1_xboole_0=B_906 | ~m1_subset_1(B_906, k1_zfmisc_1(A_905)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.74/3.31  tff(c_10121, plain, (![D_51]: (r2_hidden('#skF_7', D_51) | ~r2_hidden(D_51, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_105, c_72])).
% 8.74/3.31  tff(c_11982, plain, (![A_905]: (r2_hidden('#skF_7', '#skF_4'(A_905, '#skF_8')) | k1_xboole_0='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_905)))), inference(resolution, [status(thm)], [c_11946, c_10121])).
% 8.74/3.31  tff(c_12932, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_11982])).
% 8.74/3.31  tff(c_11363, plain, (![A_861, B_862, C_863]: (k8_subset_1(A_861, B_862, C_863)=k3_xboole_0(B_862, C_863) | ~m1_subset_1(B_862, k1_zfmisc_1(A_861)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.74/3.31  tff(c_11380, plain, (![A_864, C_865]: (k8_subset_1(A_864, k1_xboole_0, C_865)=k3_xboole_0(k1_xboole_0, C_865))), inference(resolution, [status(thm)], [c_38, c_11363])).
% 8.74/3.31  tff(c_10938, plain, (![A_34]: (k8_subset_1(A_34, k1_xboole_0, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_10929])).
% 8.74/3.31  tff(c_11391, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11380, c_10938])).
% 8.74/3.31  tff(c_95, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.74/3.31  tff(c_103, plain, (![A_34]: (r1_tarski(k1_xboole_0, A_34))), inference(resolution, [status(thm)], [c_38, c_95])).
% 8.74/3.31  tff(c_11010, plain, (![C_820, B_821, A_822]: (r2_hidden(C_820, B_821) | ~r2_hidden(C_820, A_822) | ~r1_tarski(A_822, B_821))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_11153, plain, (![A_836, B_837]: (r2_hidden('#skF_1'(A_836), B_837) | ~r1_tarski(A_836, B_837) | v1_xboole_0(A_836))), inference(resolution, [status(thm)], [c_4, c_11010])).
% 8.74/3.31  tff(c_11170, plain, (![B_838, A_839]: (~v1_xboole_0(B_838) | ~r1_tarski(A_839, B_838) | v1_xboole_0(A_839))), inference(resolution, [status(thm)], [c_11153, c_16])).
% 8.74/3.31  tff(c_11201, plain, (![A_34]: (~v1_xboole_0(A_34) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_103, c_11170])).
% 8.74/3.31  tff(c_11202, plain, (![A_34]: (~v1_xboole_0(A_34))), inference(splitLeft, [status(thm)], [c_11201])).
% 8.74/3.31  tff(c_11220, plain, (![A_70, B_71]: (~r1_xboole_0(A_70, B_71))), inference(negUnitSimplification, [status(thm)], [c_11202, c_124])).
% 8.74/3.31  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_11223, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), k3_xboole_0(A_10, B_11)))), inference(negUnitSimplification, [status(thm)], [c_11220, c_12])).
% 8.74/3.31  tff(c_11407, plain, (r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11391, c_11223])).
% 8.74/3.31  tff(c_11261, plain, (![A_852, C_853, B_854]: (m1_subset_1(A_852, C_853) | ~m1_subset_1(B_854, k1_zfmisc_1(C_853)) | ~r2_hidden(A_852, B_854))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.74/3.31  tff(c_11270, plain, (![A_852, A_34]: (m1_subset_1(A_852, A_34) | ~r2_hidden(A_852, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_11261])).
% 8.74/3.31  tff(c_11475, plain, (![A_869]: (m1_subset_1('#skF_3'(k1_xboole_0, k1_xboole_0), A_869))), inference(resolution, [status(thm)], [c_11407, c_11270])).
% 8.74/3.31  tff(c_46, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.74/3.31  tff(c_11497, plain, (![B_40]: (r1_tarski('#skF_3'(k1_xboole_0, k1_xboole_0), B_40))), inference(resolution, [status(thm)], [c_11475, c_46])).
% 8.74/3.31  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_11460, plain, (![B_6]: (r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0), B_6) | ~r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_11407, c_6])).
% 8.74/3.31  tff(c_11505, plain, (![B_870]: (r2_hidden('#skF_3'(k1_xboole_0, k1_xboole_0), B_870))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_11460])).
% 8.74/3.31  tff(c_11523, plain, (r2_hidden('#skF_7', '#skF_3'(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_11505, c_10121])).
% 8.74/3.31  tff(c_11530, plain, (![B_6]: (r2_hidden('#skF_7', B_6) | ~r1_tarski('#skF_3'(k1_xboole_0, k1_xboole_0), B_6))), inference(resolution, [status(thm)], [c_11523, c_6])).
% 8.74/3.31  tff(c_11533, plain, (![B_6]: (r2_hidden('#skF_7', B_6))), inference(demodulation, [status(thm), theory('equality')], [c_11497, c_11530])).
% 8.74/3.31  tff(c_11570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11533, c_105])).
% 8.74/3.31  tff(c_11571, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_11201])).
% 8.74/3.31  tff(c_12734, plain, (![A_957, C_958]: (k8_subset_1(A_957, k1_xboole_0, C_958)=k3_xboole_0(k1_xboole_0, C_958))), inference(resolution, [status(thm)], [c_38, c_12613])).
% 8.74/3.31  tff(c_12745, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12734, c_10938])).
% 8.74/3.31  tff(c_11110, plain, (![A_827, B_828]: (r2_hidden('#skF_3'(A_827, B_828), k3_xboole_0(A_827, B_828)) | r1_xboole_0(A_827, B_828))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_11121, plain, (![A_827, B_828]: (~v1_xboole_0(k3_xboole_0(A_827, B_828)) | r1_xboole_0(A_827, B_828))), inference(resolution, [status(thm)], [c_11110, c_16])).
% 8.74/3.31  tff(c_12767, plain, (~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12745, c_11121])).
% 8.74/3.31  tff(c_12783, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11571, c_12767])).
% 8.74/3.31  tff(c_12937, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12932, c_12932, c_12783])).
% 8.74/3.31  tff(c_12959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12690, c_12937])).
% 8.74/3.31  tff(c_12961, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_11982])).
% 8.74/3.31  tff(c_11733, plain, (![A_885, B_886]: (k6_setfam_1(A_885, B_886)=k1_setfam_1(B_886) | ~m1_subset_1(B_886, k1_zfmisc_1(k1_zfmisc_1(A_885))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.74/3.31  tff(c_11746, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_11733])).
% 8.74/3.31  tff(c_13008, plain, (![A_965, B_966]: (k8_setfam_1(A_965, B_966)=k6_setfam_1(A_965, B_966) | k1_xboole_0=B_966 | ~m1_subset_1(B_966, k1_zfmisc_1(k1_zfmisc_1(A_965))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.74/3.31  tff(c_13031, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_60, c_13008])).
% 8.74/3.31  tff(c_13042, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11746, c_13031])).
% 8.74/3.31  tff(c_13043, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_12961, c_13042])).
% 8.74/3.31  tff(c_13088, plain, (~r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_13043, c_105])).
% 8.74/3.31  tff(c_12358, plain, (![A_934, B_935]: (r2_hidden('#skF_5'(A_934, B_935), A_934) | r1_tarski(B_935, k1_setfam_1(A_934)) | k1_xboole_0=A_934)), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.74/3.31  tff(c_12399, plain, (![B_935]: (r2_hidden('#skF_7', '#skF_5'('#skF_8', B_935)) | r1_tarski(B_935, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_12358, c_10121])).
% 8.74/3.31  tff(c_13405, plain, (![B_935]: (r2_hidden('#skF_7', '#skF_5'('#skF_8', B_935)) | r1_tarski(B_935, k1_setfam_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_12961, c_12399])).
% 8.74/3.31  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.74/3.31  tff(c_11840, plain, (![B_895, A_896]: (~r1_tarski(B_895, '#skF_5'(A_896, B_895)) | r1_tarski(B_895, k1_setfam_1(A_896)) | k1_xboole_0=A_896)), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.74/3.31  tff(c_14790, plain, (![A_1036, A_1037]: (r1_tarski(k1_tarski(A_1036), k1_setfam_1(A_1037)) | k1_xboole_0=A_1037 | ~r2_hidden(A_1036, '#skF_5'(A_1037, k1_tarski(A_1036))))), inference(resolution, [status(thm)], [c_20, c_11840])).
% 8.74/3.31  tff(c_14802, plain, (k1_xboole_0='#skF_8' | r1_tarski(k1_tarski('#skF_7'), k1_setfam_1('#skF_8'))), inference(resolution, [status(thm)], [c_13405, c_14790])).
% 8.74/3.31  tff(c_14819, plain, (r1_tarski(k1_tarski('#skF_7'), k1_setfam_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_12961, c_14802])).
% 8.74/3.31  tff(c_18, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.74/3.31  tff(c_14845, plain, (r2_hidden('#skF_7', k1_setfam_1('#skF_8'))), inference(resolution, [status(thm)], [c_14819, c_18])).
% 8.74/3.31  tff(c_14864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13088, c_14845])).
% 8.74/3.31  tff(c_14866, plain, (r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_64])).
% 8.74/3.31  tff(c_62, plain, (~r2_hidden('#skF_7', '#skF_9') | ~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.74/3.31  tff(c_14871, plain, (~r2_hidden('#skF_7', k8_setfam_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_62])).
% 8.74/3.31  tff(c_14877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14866, c_14871])).
% 8.74/3.31  tff(c_14878, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 8.74/3.31  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_14922, plain, (![A_1057, B_1058]: (~r2_hidden('#skF_2'(A_1057, B_1058), B_1058) | r1_tarski(A_1057, B_1058))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_14927, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_14922])).
% 8.74/3.31  tff(c_14865, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 8.74/3.31  tff(c_15010, plain, (![C_1073, B_1074, A_1075]: (r2_hidden(C_1073, B_1074) | ~r2_hidden(C_1073, A_1075) | ~r1_tarski(A_1075, B_1074))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.74/3.31  tff(c_15026, plain, (![B_1074]: (r2_hidden('#skF_9', B_1074) | ~r1_tarski('#skF_8', B_1074))), inference(resolution, [status(thm)], [c_14865, c_15010])).
% 8.74/3.31  tff(c_50, plain, (![B_42, A_41]: (r1_tarski(k1_setfam_1(B_42), A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.74/3.31  tff(c_16470, plain, (![A_1176, B_1177, C_1178]: (k8_subset_1(A_1176, B_1177, C_1178)=k3_xboole_0(B_1177, C_1178) | ~m1_subset_1(B_1177, k1_zfmisc_1(A_1176)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.74/3.31  tff(c_16502, plain, (![C_1180]: (k8_subset_1(k1_zfmisc_1('#skF_6'), '#skF_8', C_1180)=k3_xboole_0('#skF_8', C_1180))), inference(resolution, [status(thm)], [c_60, c_16470])).
% 8.74/3.31  tff(c_14941, plain, (![A_1065, B_1066]: (k8_subset_1(A_1065, B_1066, B_1066)=B_1066 | ~m1_subset_1(B_1066, k1_zfmisc_1(A_1065)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.74/3.31  tff(c_14949, plain, (k8_subset_1(k1_zfmisc_1('#skF_6'), '#skF_8', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_60, c_14941])).
% 8.74/3.31  tff(c_16508, plain, (k3_xboole_0('#skF_8', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_16502, c_14949])).
% 8.74/3.31  tff(c_15029, plain, (![B_1076]: (r2_hidden('#skF_9', B_1076) | ~r1_tarski('#skF_8', B_1076))), inference(resolution, [status(thm)], [c_14865, c_15010])).
% 8.74/3.31  tff(c_15040, plain, (![A_10, B_11]: (~r1_xboole_0(A_10, B_11) | ~r1_tarski('#skF_8', k3_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_15029, c_14])).
% 8.74/3.31  tff(c_16523, plain, (~r1_xboole_0('#skF_8', '#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_16508, c_15040])).
% 8.74/3.31  tff(c_16542, plain, (~r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14927, c_16523])).
% 8.74/3.31  tff(c_15141, plain, (![A_1091, B_1092]: (k6_setfam_1(A_1091, B_1092)=k1_setfam_1(B_1092) | ~m1_subset_1(B_1092, k1_zfmisc_1(k1_zfmisc_1(A_1091))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.74/3.31  tff(c_15154, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_15141])).
% 8.74/3.31  tff(c_17292, plain, (![A_1218, B_1219]: (k8_setfam_1(A_1218, B_1219)=k6_setfam_1(A_1218, B_1219) | k1_xboole_0=B_1219 | ~m1_subset_1(B_1219, k1_zfmisc_1(k1_zfmisc_1(A_1218))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.74/3.31  tff(c_17303, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_60, c_17292])).
% 8.74/3.31  tff(c_17311, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15154, c_17303])).
% 8.74/3.31  tff(c_17315, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_17311])).
% 8.74/3.31  tff(c_15979, plain, (![A_1155, B_1156]: (k1_subset_1(A_1155)=B_1156 | ~r1_tarski(B_1156, k3_subset_1(A_1155, B_1156)) | ~m1_subset_1(B_1156, k1_zfmisc_1(A_1155)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.74/3.31  tff(c_16010, plain, (![A_1155]: (k1_subset_1(A_1155)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1155)))), inference(resolution, [status(thm)], [c_103, c_15979])).
% 8.74/3.31  tff(c_16027, plain, (![A_1155]: (k1_subset_1(A_1155)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_16010])).
% 8.74/3.31  tff(c_15128, plain, (![A_1089, B_1090]: (r2_hidden('#skF_1'(A_1089), B_1090) | ~r1_tarski(A_1089, B_1090) | v1_xboole_0(A_1089))), inference(resolution, [status(thm)], [c_4, c_15010])).
% 8.74/3.31  tff(c_15167, plain, (![B_1094, A_1095]: (~v1_xboole_0(B_1094) | ~r1_tarski(A_1095, B_1094) | v1_xboole_0(A_1095))), inference(resolution, [status(thm)], [c_15128, c_16])).
% 8.74/3.31  tff(c_15197, plain, (![A_34]: (~v1_xboole_0(A_34) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_103, c_15167])).
% 8.74/3.31  tff(c_15220, plain, (![A_34]: (~v1_xboole_0(A_34))), inference(splitLeft, [status(thm)], [c_15197])).
% 8.74/3.31  tff(c_15224, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_15220, c_4])).
% 8.74/3.31  tff(c_15297, plain, (![A_1111, C_1112, B_1113]: (m1_subset_1(A_1111, C_1112) | ~m1_subset_1(B_1113, k1_zfmisc_1(C_1112)) | ~r2_hidden(A_1111, B_1113))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.74/3.31  tff(c_15310, plain, (![A_1114, A_1115]: (m1_subset_1(A_1114, A_1115) | ~r2_hidden(A_1114, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_15297])).
% 8.74/3.31  tff(c_15327, plain, (![A_1115]: (m1_subset_1('#skF_1'(k1_xboole_0), A_1115))), inference(resolution, [status(thm)], [c_15224, c_15310])).
% 8.74/3.31  tff(c_15332, plain, (![A_1116]: (m1_subset_1('#skF_1'(k1_xboole_0), A_1116))), inference(resolution, [status(thm)], [c_15224, c_15310])).
% 8.74/3.31  tff(c_15350, plain, (![B_40]: (r1_tarski('#skF_1'(k1_xboole_0), B_40))), inference(resolution, [status(thm)], [c_15332, c_46])).
% 8.74/3.31  tff(c_15998, plain, (![A_1155]: (k1_subset_1(A_1155)='#skF_1'(k1_xboole_0) | ~m1_subset_1('#skF_1'(k1_xboole_0), k1_zfmisc_1(A_1155)))), inference(resolution, [status(thm)], [c_15350, c_15979])).
% 8.74/3.31  tff(c_16022, plain, (![A_1155]: (k1_subset_1(A_1155)='#skF_1'(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_15327, c_15998])).
% 8.74/3.31  tff(c_16039, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16027, c_16022])).
% 8.74/3.31  tff(c_52, plain, (![A_43, C_45, B_44]: (m1_subset_1(A_43, C_45) | ~m1_subset_1(B_44, k1_zfmisc_1(C_45)) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.74/3.31  tff(c_15528, plain, (![A_1128, C_1129]: (m1_subset_1(A_1128, C_1129) | ~r2_hidden(A_1128, '#skF_1'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_15332, c_52])).
% 8.74/3.31  tff(c_15551, plain, (![C_1129]: (m1_subset_1('#skF_1'('#skF_1'(k1_xboole_0)), C_1129))), inference(resolution, [status(thm)], [c_15224, c_15528])).
% 8.74/3.31  tff(c_16043, plain, (![C_1129]: (m1_subset_1(k1_xboole_0, C_1129))), inference(demodulation, [status(thm), theory('equality')], [c_16039, c_16039, c_15551])).
% 8.74/3.31  tff(c_14898, plain, (![A_1046, B_1047, C_1048]: (~r1_xboole_0(A_1046, B_1047) | ~r2_hidden(C_1048, k3_xboole_0(A_1046, B_1047)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_14903, plain, (![A_1046, B_1047]: (~r1_xboole_0(A_1046, B_1047) | v1_xboole_0(k3_xboole_0(A_1046, B_1047)))), inference(resolution, [status(thm)], [c_4, c_14898])).
% 8.74/3.31  tff(c_15223, plain, (![A_1046, B_1047]: (~r1_xboole_0(A_1046, B_1047))), inference(negUnitSimplification, [status(thm)], [c_15220, c_14903])).
% 8.74/3.31  tff(c_34, plain, (![B_31, C_33, A_30]: (r1_xboole_0(B_31, C_33) | ~r1_tarski(B_31, k3_subset_1(A_30, C_33)) | ~m1_subset_1(C_33, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.74/3.31  tff(c_16294, plain, (![B_1164, A_1165, C_1166]: (~r1_tarski(B_1164, k3_subset_1(A_1165, C_1166)) | ~m1_subset_1(C_1166, k1_zfmisc_1(A_1165)) | ~m1_subset_1(B_1164, k1_zfmisc_1(A_1165)))), inference(negUnitSimplification, [status(thm)], [c_15223, c_34])).
% 8.74/3.31  tff(c_16314, plain, (![C_1166, A_1165]: (~m1_subset_1(C_1166, k1_zfmisc_1(A_1165)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1165)))), inference(resolution, [status(thm)], [c_103, c_16294])).
% 8.74/3.31  tff(c_16321, plain, (![C_1166, A_1165]: (~m1_subset_1(C_1166, k1_zfmisc_1(A_1165)))), inference(demodulation, [status(thm), theory('equality')], [c_16043, c_16314])).
% 8.74/3.31  tff(c_16325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16321, c_60])).
% 8.74/3.31  tff(c_16326, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_15197])).
% 8.74/3.31  tff(c_16572, plain, (![A_1183, C_1184]: (k8_subset_1(A_1183, k1_xboole_0, C_1184)=k3_xboole_0(k1_xboole_0, C_1184))), inference(resolution, [status(thm)], [c_38, c_16470])).
% 8.74/3.31  tff(c_14950, plain, (![A_34]: (k8_subset_1(A_34, k1_xboole_0, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_14941])).
% 8.74/3.31  tff(c_16583, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16572, c_14950])).
% 8.74/3.31  tff(c_15057, plain, (![A_1078, B_1079]: (r2_hidden('#skF_3'(A_1078, B_1079), k3_xboole_0(A_1078, B_1079)) | r1_xboole_0(A_1078, B_1079))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.74/3.31  tff(c_15068, plain, (![A_1078, B_1079]: (~v1_xboole_0(k3_xboole_0(A_1078, B_1079)) | r1_xboole_0(A_1078, B_1079))), inference(resolution, [status(thm)], [c_15057, c_16])).
% 8.74/3.31  tff(c_16605, plain, (~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16583, c_15068])).
% 8.74/3.31  tff(c_16621, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16326, c_16605])).
% 8.74/3.31  tff(c_17329, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17315, c_17315, c_16621])).
% 8.74/3.31  tff(c_17342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16542, c_17329])).
% 8.74/3.31  tff(c_17343, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(splitRight, [status(thm)], [c_17311])).
% 8.74/3.31  tff(c_15025, plain, (![B_1074]: (r2_hidden('#skF_7', B_1074) | ~r1_tarski(k8_setfam_1('#skF_6', '#skF_8'), B_1074))), inference(resolution, [status(thm)], [c_14866, c_15010])).
% 8.74/3.31  tff(c_17445, plain, (![B_1225]: (r2_hidden('#skF_7', B_1225) | ~r1_tarski(k1_setfam_1('#skF_8'), B_1225))), inference(demodulation, [status(thm), theory('equality')], [c_17343, c_15025])).
% 8.74/3.31  tff(c_17467, plain, (![A_1226]: (r2_hidden('#skF_7', A_1226) | ~r2_hidden(A_1226, '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_17445])).
% 8.74/3.31  tff(c_17487, plain, (r2_hidden('#skF_7', '#skF_9') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_15026, c_17467])).
% 8.74/3.31  tff(c_17510, plain, (r2_hidden('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14927, c_17487])).
% 8.74/3.31  tff(c_17512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14878, c_17510])).
% 8.74/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.31  
% 8.74/3.31  Inference rules
% 8.74/3.31  ----------------------
% 8.74/3.31  #Ref     : 0
% 8.74/3.31  #Sup     : 3969
% 8.74/3.31  #Fact    : 0
% 8.74/3.31  #Define  : 0
% 8.74/3.31  #Split   : 91
% 8.74/3.31  #Chain   : 0
% 8.74/3.31  #Close   : 0
% 8.74/3.31  
% 8.74/3.31  Ordering : KBO
% 8.74/3.31  
% 8.74/3.31  Simplification rules
% 8.74/3.31  ----------------------
% 8.74/3.31  #Subsume      : 927
% 8.74/3.31  #Demod        : 1319
% 8.74/3.31  #Tautology    : 1126
% 8.74/3.31  #SimpNegUnit  : 172
% 8.74/3.31  #BackRed      : 267
% 8.74/3.31  
% 8.74/3.31  #Partial instantiations: 0
% 8.74/3.31  #Strategies tried      : 1
% 8.74/3.31  
% 8.74/3.31  Timing (in seconds)
% 8.74/3.31  ----------------------
% 8.74/3.31  Preprocessing        : 0.36
% 8.74/3.31  Parsing              : 0.19
% 8.74/3.31  CNF conversion       : 0.03
% 8.74/3.31  Main loop            : 2.14
% 8.74/3.31  Inferencing          : 0.71
% 8.74/3.31  Reduction            : 0.68
% 8.74/3.31  Demodulation         : 0.44
% 8.74/3.31  BG Simplification    : 0.07
% 8.74/3.31  Subsumption          : 0.47
% 8.74/3.31  Abstraction          : 0.09
% 8.74/3.31  MUC search           : 0.00
% 8.74/3.31  Cooper               : 0.00
% 8.74/3.31  Total                : 2.57
% 8.74/3.31  Index Insertion      : 0.00
% 8.74/3.31  Index Deletion       : 0.00
% 8.74/3.31  Index Matching       : 0.00
% 8.74/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
