%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1292+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:44 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 108 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 185 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > o_2_0_tops_2 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(o_2_0_tops_2,type,(
    o_2_0_tops_2: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_51,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ! [A_24] : m1_subset_1('#skF_5'(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    m1_setfam_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_92,plain,(
    ! [A_55,B_56] :
      ( k5_setfam_1(A_55,B_56) = k3_tarski(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,(
    k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7') = k3_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_156,plain,(
    ! [A_65,B_66] :
      ( k5_setfam_1(A_65,B_66) = A_65
      | ~ m1_setfam_1(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_163,plain,
    ( k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7') = u1_struct_0('#skF_6')
    | ~ m1_setfam_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_171,plain,(
    u1_struct_0('#skF_6') = k3_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_100,c_163])).

tff(c_28,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,
    ( ~ v1_xboole_0(k3_tarski('#skF_7'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_28])).

tff(c_186,plain,
    ( ~ v1_xboole_0(k3_tarski('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_182])).

tff(c_187,plain,(
    ~ v1_xboole_0(k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_186])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,C_16] :
      ( r2_hidden('#skF_4'(A_1,k3_tarski(A_1),C_16),A_1)
      | ~ r2_hidden(C_16,k3_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,(
    ! [C_50,A_51] :
      ( ~ v1_xboole_0(C_50)
      | ~ r2_hidden(A_51,'#skF_5'(k1_zfmisc_1(C_50))) ) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_330,plain,(
    ! [C_83,A_84] :
      ( ~ v1_xboole_0(C_83)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_83)))
      | ~ m1_subset_1(A_84,'#skF_5'(k1_zfmisc_1(C_83))) ) ),
    inference(resolution,[status(thm)],[c_34,c_82])).

tff(c_415,plain,(
    ! [C_87] :
      ( ~ v1_xboole_0(C_87)
      | v1_xboole_0('#skF_5'(k1_zfmisc_1(C_87))) ) ),
    inference(resolution,[status(thm)],[c_24,c_330])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_53,plain,(
    ! [A_38] :
      ( A_38 = '#skF_7'
      | ~ v1_xboole_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_420,plain,(
    ! [C_88] :
      ( '#skF_5'(k1_zfmisc_1(C_88)) = '#skF_7'
      | ~ v1_xboole_0(C_88) ) ),
    inference(resolution,[status(thm)],[c_415,c_53])).

tff(c_460,plain,(
    ! [C_89] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(C_89))
      | ~ v1_xboole_0(C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_24])).

tff(c_36,plain,(
    ! [C_35,B_34,A_33] :
      ( ~ v1_xboole_0(C_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_35))
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_478,plain,(
    ! [A_33,C_89] :
      ( ~ r2_hidden(A_33,'#skF_7')
      | ~ v1_xboole_0(C_89) ) ),
    inference(resolution,[status(thm)],[c_460,c_36])).

tff(c_517,plain,(
    ! [C_89] : ~ v1_xboole_0(C_89) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_26])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_54])).

tff(c_523,plain,(
    ! [A_92] : ~ r2_hidden(A_92,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_547,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4,c_523])).

tff(c_567,plain,(
    ! [A_31] :
      ( v1_xboole_0(k3_tarski('#skF_7'))
      | ~ m1_subset_1(A_31,k3_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_34,c_547])).

tff(c_575,plain,(
    ! [A_94] : ~ m1_subset_1(A_94,k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_567])).

tff(c_585,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_575])).

%------------------------------------------------------------------------------
