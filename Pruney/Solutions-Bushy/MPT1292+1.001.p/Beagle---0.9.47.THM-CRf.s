%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1292+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:44 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   55 (  61 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 (  92 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_38,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_36,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22])).

tff(c_20,plain,(
    ! [A_20] : m1_subset_1('#skF_5'(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [A_47,C_48] :
      ( r2_hidden('#skF_4'(A_47,k3_tarski(A_47),C_48),A_47)
      | ~ r2_hidden(C_48,k3_tarski(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( ~ v1_xboole_0(B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    ! [A_49,C_50] :
      ( ~ v1_xboole_0(A_49)
      | ~ r2_hidden(C_50,k3_tarski(A_49)) ) ),
    inference(resolution,[status(thm)],[c_85,c_34])).

tff(c_179,plain,(
    ! [A_59,A_60] :
      ( ~ v1_xboole_0(A_59)
      | v1_xboole_0(k3_tarski(A_59))
      | ~ m1_subset_1(A_60,k3_tarski(A_59)) ) ),
    inference(resolution,[status(thm)],[c_28,c_93])).

tff(c_207,plain,(
    ! [A_63] :
      ( ~ v1_xboole_0(A_63)
      | v1_xboole_0(k3_tarski(A_63)) ) ),
    inference(resolution,[status(thm)],[c_20,c_179])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    m1_setfam_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    ! [A_41,B_42] :
      ( k5_setfam_1(A_41,B_42) = k3_tarski(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7') = k3_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_126,plain,(
    ! [A_55,B_56] :
      ( k5_setfam_1(A_55,B_56) = A_55
      | ~ m1_setfam_1(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_129,plain,
    ( k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7') = u1_struct_0('#skF_6')
    | ~ m1_setfam_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_126])).

tff(c_136,plain,(
    u1_struct_0('#skF_6') = k3_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70,c_129])).

tff(c_24,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,
    ( ~ v1_xboole_0(k3_tarski('#skF_7'))
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_24])).

tff(c_148,plain,
    ( ~ v1_xboole_0(k3_tarski('#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_144])).

tff(c_149,plain,(
    ~ v1_xboole_0(k3_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_148])).

tff(c_210,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_207,c_149])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_210])).

%------------------------------------------------------------------------------
