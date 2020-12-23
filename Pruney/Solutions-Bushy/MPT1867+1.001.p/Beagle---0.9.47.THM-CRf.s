%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1867+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:34 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 125 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 285 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(f_70,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_63,axiom,(
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

tff(f_78,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_40,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_34] : v1_xboole_0('#skF_3'(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61,plain,(
    ! [A_49] :
      ( A_49 = '#skF_5'
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_68,plain,(
    ! [A_34] : '#skF_3'(A_34) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_22,plain,(
    ! [A_34] : m1_subset_1('#skF_3'(A_34),k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [A_34] : m1_subset_1('#skF_5',k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22])).

tff(c_154,plain,(
    ! [A_74,B_75] :
      ( r1_tarski('#skF_2'(A_74,B_75),B_75)
      | v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_163,plain,(
    ! [A_76] :
      ( r1_tarski('#skF_2'(A_76,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_71,c_154])).

tff(c_28,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(A_39,k1_zfmisc_1(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_95,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_39,B_40] :
      ( v1_xboole_0(A_39)
      | ~ v1_xboole_0(B_40)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_168,plain,(
    ! [A_76] :
      ( v1_xboole_0('#skF_2'(A_76,'#skF_5'))
      | ~ v1_xboole_0('#skF_5')
      | v2_tex_2('#skF_5',A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_163,c_102])).

tff(c_173,plain,(
    ! [A_77] :
      ( v1_xboole_0('#skF_2'(A_77,'#skF_5'))
      | v2_tex_2('#skF_5',A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_168])).

tff(c_60,plain,(
    ! [A_48] :
      ( A_48 = '#skF_5'
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_181,plain,(
    ! [A_78] :
      ( '#skF_2'(A_78,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_173,c_60])).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_184,plain,
    ( '#skF_2'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_181,c_32])).

tff(c_187,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_184])).

tff(c_132,plain,(
    ! [B_69,A_70] :
      ( v3_pre_topc(B_69,A_70)
      | ~ v1_xboole_0(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,(
    ! [A_70] :
      ( v3_pre_topc('#skF_5',A_70)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_71,c_132])).

tff(c_144,plain,(
    ! [A_70] :
      ( v3_pre_topc('#skF_5',A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_140])).

tff(c_18,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_111,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,C_63) = k3_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_117,plain,(
    ! [A_34,B_62] : k9_subset_1(A_34,B_62,'#skF_5') = k3_xboole_0(B_62,'#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_111])).

tff(c_500,plain,(
    ! [A_107,B_108,D_109] :
      ( k9_subset_1(u1_struct_0(A_107),B_108,D_109) != '#skF_2'(A_107,B_108)
      | ~ v3_pre_topc(D_109,A_107)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_503,plain,(
    ! [B_62,A_107] :
      ( k3_xboole_0(B_62,'#skF_5') != '#skF_2'(A_107,B_62)
      | ~ v3_pre_topc('#skF_5',A_107)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_107)))
      | v2_tex_2(B_62,A_107)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_500])).

tff(c_576,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(B_115,'#skF_5') != '#skF_2'(A_116,B_115)
      | ~ v3_pre_topc('#skF_5',A_116)
      | v2_tex_2(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_503])).

tff(c_593,plain,(
    ! [A_116] :
      ( k3_xboole_0('#skF_5','#skF_5') != '#skF_2'(A_116,'#skF_5')
      | ~ v3_pre_topc('#skF_5',A_116)
      | v2_tex_2('#skF_5',A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_71,c_576])).

tff(c_600,plain,(
    ! [A_117] :
      ( '#skF_2'(A_117,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_117)
      | v2_tex_2('#skF_5',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_593])).

tff(c_605,plain,(
    ! [A_118] :
      ( '#skF_2'(A_118,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_144,c_600])).

tff(c_608,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_605,c_32])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_187,c_608])).

%------------------------------------------------------------------------------
