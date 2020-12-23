%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1867+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:35 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 173 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 351 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_78,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_20,plain,(
    ! [A_35] : v1_xboole_0('#skF_3'(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_53,plain,(
    ! [A_35] : '#skF_3'(A_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_60,plain,(
    ! [A_35] : '#skF_3'(A_35) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53])).

tff(c_22,plain,(
    ! [A_35] : m1_subset_1('#skF_3'(A_35),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ! [A_35] : m1_subset_1('#skF_5',k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_175,plain,(
    ! [A_78,B_79] :
      ( r1_tarski('#skF_2'(A_78,B_79),B_79)
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_185,plain,(
    ! [A_81] :
      ( r1_tarski('#skF_2'(A_81,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_84,c_175])).

tff(c_30,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_97,plain,(
    ! [B_55,A_56] :
      ( v1_xboole_0(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( v1_xboole_0(A_41)
      | ~ v1_xboole_0(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_30,c_97])).

tff(c_192,plain,(
    ! [A_81] :
      ( v1_xboole_0('#skF_2'(A_81,'#skF_5'))
      | ~ v1_xboole_0('#skF_5')
      | v2_tex_2('#skF_5',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_185,c_104])).

tff(c_198,plain,(
    ! [A_82] :
      ( v1_xboole_0('#skF_2'(A_82,'#skF_5'))
      | v2_tex_2('#skF_5',A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_192])).

tff(c_32,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    ! [A_43] :
      ( A_43 = '#skF_5'
      | ~ v1_xboole_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_225,plain,(
    ! [A_85] :
      ( '#skF_2'(A_85,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_198,c_55])).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_228,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_225,c_34])).

tff(c_231,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_228])).

tff(c_162,plain,(
    ! [B_76,A_77] :
      ( v3_pre_topc(B_76,A_77)
      | ~ v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,(
    ! [A_77] :
      ( v3_pre_topc('#skF_5',A_77)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_84,c_162])).

tff(c_174,plain,(
    ! [A_77] :
      ( v3_pre_topc('#skF_5',A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_170])).

tff(c_26,plain,(
    ! [A_40] : k3_xboole_0(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_70,plain,(
    ! [A_40] : k3_xboole_0(A_40,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_26])).

tff(c_114,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_118,plain,(
    ! [A_35,B_61] : k9_subset_1(A_35,B_61,'#skF_5') = k3_xboole_0(B_61,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_114])).

tff(c_121,plain,(
    ! [A_35,B_61] : k9_subset_1(A_35,B_61,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_118])).

tff(c_122,plain,(
    ! [A_63,C_64,B_65] :
      ( k9_subset_1(A_63,C_64,B_65) = k9_subset_1(A_63,B_65,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_128,plain,(
    ! [A_35,B_65] : k9_subset_1(A_35,B_65,'#skF_5') = k9_subset_1(A_35,'#skF_5',B_65) ),
    inference(resolution,[status(thm)],[c_84,c_122])).

tff(c_136,plain,(
    ! [A_35,B_65] : k9_subset_1(A_35,'#skF_5',B_65) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_128])).

tff(c_435,plain,(
    ! [A_110,B_111,D_112] :
      ( k9_subset_1(u1_struct_0(A_110),B_111,D_112) != '#skF_2'(A_110,B_111)
      | ~ v3_pre_topc(D_112,A_110)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0(A_110)))
      | v2_tex_2(B_111,A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_438,plain,(
    ! [A_110,B_65] :
      ( '#skF_2'(A_110,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc(B_65,A_110)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_110)))
      | v2_tex_2('#skF_5',A_110)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_435])).

tff(c_551,plain,(
    ! [A_120,B_121] :
      ( '#skF_2'(A_120,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | v2_tex_2('#skF_5',A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_438])).

tff(c_570,plain,(
    ! [A_122] :
      ( '#skF_2'(A_122,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_122)
      | v2_tex_2('#skF_5',A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_84,c_551])).

tff(c_575,plain,(
    ! [A_123] :
      ( '#skF_2'(A_123,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_174,c_570])).

tff(c_578,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_575,c_34])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_231,c_578])).

%------------------------------------------------------------------------------
