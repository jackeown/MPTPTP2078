%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1861+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:34 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   57 (  97 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 203 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_73,plain,(
    ! [A_31,B_32,C_33] :
      ( k9_subset_1(A_31,B_32,C_33) = k3_xboole_0(B_32,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [B_40] : k9_subset_1(u1_struct_0('#skF_1'),B_40,'#skF_2') = k3_xboole_0(B_40,'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_73])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_139,plain,(
    ! [B_40] :
      ( m1_subset_1(k3_xboole_0(B_40,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_4])).

tff(c_147,plain,(
    ! [B_41] : m1_subset_1(k3_xboole_0(B_41,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_139])).

tff(c_153,plain,(
    ! [A_1] : m1_subset_1(k3_xboole_0('#skF_2',A_1),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [C_36,A_37,B_38] :
      ( v2_tex_2(C_36,A_37)
      | ~ v2_tex_2(B_38,A_37)
      | ~ r1_tarski(C_36,B_38)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_393,plain,(
    ! [A_63,B_64,A_65] :
      ( v2_tex_2(k3_xboole_0(A_63,B_64),A_65)
      | ~ v2_tex_2(A_63,A_65)
      | ~ m1_subset_1(k3_xboole_0(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(A_63,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_414,plain,(
    ! [A_1] :
      ( v2_tex_2(k3_xboole_0('#skF_2',A_1),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_153,c_393])).

tff(c_460,plain,(
    ! [A_66] : v2_tex_2(k3_xboole_0('#skF_2',A_66),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_22,c_414])).

tff(c_464,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0(B_2,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_460])).

tff(c_81,plain,(
    ! [B_32] : k9_subset_1(u1_struct_0('#skF_1'),B_32,'#skF_3') = k3_xboole_0(B_32,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_73])).

tff(c_12,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_83,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_84,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_84])).

tff(c_472,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_523,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,C_73) = k3_xboole_0(B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_536,plain,(
    ! [B_77] : k9_subset_1(u1_struct_0('#skF_1'),B_77,'#skF_3') = k3_xboole_0(B_77,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_523])).

tff(c_542,plain,(
    ! [B_77] :
      ( m1_subset_1(k3_xboole_0(B_77,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_4])).

tff(c_550,plain,(
    ! [B_78] : m1_subset_1(k3_xboole_0(B_78,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_542])).

tff(c_560,plain,(
    ! [B_2] : m1_subset_1(k3_xboole_0('#skF_3',B_2),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_550])).

tff(c_618,plain,(
    ! [C_83,A_84,B_85] :
      ( v2_tex_2(C_83,A_84)
      | ~ v2_tex_2(B_85,A_84)
      | ~ r1_tarski(C_83,B_85)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_946,plain,(
    ! [A_112,B_113,A_114] :
      ( v2_tex_2(k3_xboole_0(A_112,B_113),A_114)
      | ~ v2_tex_2(A_112,A_114)
      | ~ m1_subset_1(k3_xboole_0(A_112,B_113),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(A_112,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_8,c_618])).

tff(c_976,plain,(
    ! [B_2] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_2),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_560,c_946])).

tff(c_1018,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0('#skF_3',B_2),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_472,c_976])).

tff(c_528,plain,(
    ! [B_72] : k9_subset_1(u1_struct_0('#skF_1'),B_72,'#skF_3') = k3_xboole_0(B_72,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_523])).

tff(c_534,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_12])).

tff(c_535,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_534])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_535])).

%------------------------------------------------------------------------------
