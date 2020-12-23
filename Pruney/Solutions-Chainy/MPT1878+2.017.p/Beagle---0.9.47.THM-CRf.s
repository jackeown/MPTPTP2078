%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:59 EST 2020

% Result     : Theorem 15.44s
% Output     : CNFRefutation 15.44s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 105 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  154 ( 240 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [B_59,A_60] :
      ( m1_subset_1(B_59,A_60)
      | ~ r2_hidden(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,(
    ! [A_63] :
      ( m1_subset_1('#skF_1'(A_63),A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_165,plain,(
    ! [A_63] :
      ( k6_domain_1(A_63,'#skF_1'(A_63)) = k1_tarski('#skF_1'(A_63))
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_158,c_32])).

tff(c_286,plain,(
    ! [A_84,B_85] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_84),B_85),A_84)
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2167,plain,(
    ! [A_231] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_231))),A_231)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_231)),u1_struct_0(A_231))
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231)
      | v1_xboole_0(u1_struct_0(A_231)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_286])).

tff(c_52,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_69,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_4') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),B_45) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_12])).

tff(c_106,plain,(
    ! [A_44] : k1_tarski(A_44) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_102])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k1_tarski(A_13),k1_zfmisc_1(B_14))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_22])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_704,plain,(
    ! [C_128,B_129,A_130] :
      ( C_128 = B_129
      | ~ r1_tarski(B_129,C_128)
      | ~ v2_tex_2(C_128,A_130)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v3_tex_2(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_706,plain,(
    ! [A_7,A_130] :
      ( A_7 = '#skF_4'
      | ~ v2_tex_2(A_7,A_130)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v3_tex_2('#skF_4',A_130)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_76,c_704])).

tff(c_710,plain,(
    ! [A_131,A_132] :
      ( A_131 = '#skF_4'
      | ~ v2_tex_2(A_131,A_132)
      | ~ m1_subset_1(A_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v3_tex_2('#skF_4',A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_706])).

tff(c_737,plain,(
    ! [A_13,A_132] :
      ( k1_tarski(A_13) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(A_13),A_132)
      | ~ v3_tex_2('#skF_4',A_132)
      | ~ l1_pre_topc(A_132)
      | ~ r2_hidden(A_13,u1_struct_0(A_132)) ) ),
    inference(resolution,[status(thm)],[c_24,c_710])).

tff(c_754,plain,(
    ! [A_13,A_132] :
      ( ~ v2_tex_2(k1_tarski(A_13),A_132)
      | ~ v3_tex_2('#skF_4',A_132)
      | ~ l1_pre_topc(A_132)
      | ~ r2_hidden(A_13,u1_struct_0(A_132)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_737])).

tff(c_24265,plain,(
    ! [A_624] :
      ( ~ v3_tex_2('#skF_4',A_624)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_624)),u1_struct_0(A_624))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_624)),u1_struct_0(A_624))
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624)
      | v1_xboole_0(u1_struct_0(A_624)) ) ),
    inference(resolution,[status(thm)],[c_2167,c_754])).

tff(c_24469,plain,(
    ! [A_627] :
      ( ~ v3_tex_2('#skF_4',A_627)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_627)),u1_struct_0(A_627))
      | v1_xboole_0(u1_struct_0(A_627)) ) ),
    inference(resolution,[status(thm)],[c_16,c_24265])).

tff(c_24483,plain,(
    ! [A_628] :
      ( ~ v3_tex_2('#skF_4',A_628)
      | ~ l1_pre_topc(A_628)
      | ~ v2_pre_topc(A_628)
      | v2_struct_0(A_628)
      | v1_xboole_0(u1_struct_0(A_628)) ) ),
    inference(resolution,[status(thm)],[c_144,c_24469])).

tff(c_30,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24496,plain,(
    ! [A_629] :
      ( ~ l1_struct_0(A_629)
      | ~ v3_tex_2('#skF_4',A_629)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(resolution,[status(thm)],[c_24483,c_30])).

tff(c_24506,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_24496])).

tff(c_24510,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_24506])).

tff(c_24511,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_24510])).

tff(c_24514,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_24511])).

tff(c_24518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_24514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.44/6.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.44/6.92  
% 15.44/6.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.44/6.93  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 15.44/6.93  
% 15.44/6.93  %Foreground sorts:
% 15.44/6.93  
% 15.44/6.93  
% 15.44/6.93  %Background operators:
% 15.44/6.93  
% 15.44/6.93  
% 15.44/6.93  %Foreground operators:
% 15.44/6.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.44/6.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.44/6.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.44/6.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.44/6.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.44/6.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.44/6.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.44/6.93  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 15.44/6.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.44/6.93  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 15.44/6.93  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 15.44/6.93  tff('#skF_3', type, '#skF_3': $i).
% 15.44/6.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.44/6.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.44/6.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.44/6.93  tff('#skF_4', type, '#skF_4': $i).
% 15.44/6.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.44/6.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.44/6.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.44/6.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.44/6.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.44/6.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.44/6.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.44/6.93  
% 15.44/6.94  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 15.44/6.94  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.44/6.94  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.44/6.94  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.44/6.94  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 15.44/6.94  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 15.44/6.94  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 15.44/6.94  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 15.44/6.94  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 15.44/6.94  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 15.44/6.94  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 15.44/6.94  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.44/6.94  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 15.44/6.94  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 15.44/6.94  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.44/6.94  tff(c_28, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.44/6.94  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.44/6.94  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.44/6.94  tff(c_48, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.44/6.94  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.44/6.94  tff(c_136, plain, (![B_59, A_60]: (m1_subset_1(B_59, A_60) | ~r2_hidden(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.44/6.94  tff(c_144, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_136])).
% 15.44/6.94  tff(c_16, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.44/6.94  tff(c_158, plain, (![A_63]: (m1_subset_1('#skF_1'(A_63), A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_4, c_136])).
% 15.44/6.94  tff(c_32, plain, (![A_20, B_21]: (k6_domain_1(A_20, B_21)=k1_tarski(B_21) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.44/6.94  tff(c_165, plain, (![A_63]: (k6_domain_1(A_63, '#skF_1'(A_63))=k1_tarski('#skF_1'(A_63)) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_158, c_32])).
% 15.44/6.94  tff(c_286, plain, (![A_84, B_85]: (v2_tex_2(k6_domain_1(u1_struct_0(A_84), B_85), A_84) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.44/6.94  tff(c_2167, plain, (![A_231]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_231))), A_231) | ~m1_subset_1('#skF_1'(u1_struct_0(A_231)), u1_struct_0(A_231)) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231) | v1_xboole_0(u1_struct_0(A_231)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_286])).
% 15.44/6.94  tff(c_52, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.44/6.94  tff(c_69, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.44/6.94  tff(c_73, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_52, c_69])).
% 15.44/6.94  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.44/6.94  tff(c_75, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_4')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_8])).
% 15.44/6.94  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.44/6.94  tff(c_102, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_12])).
% 15.44/6.94  tff(c_106, plain, (![A_44]: (k1_tarski(A_44)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75, c_102])).
% 15.44/6.94  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(k1_tarski(A_13), k1_zfmisc_1(B_14)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.44/6.94  tff(c_22, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.44/6.94  tff(c_83, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_22])).
% 15.44/6.94  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.44/6.94  tff(c_76, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_10])).
% 15.44/6.94  tff(c_704, plain, (![C_128, B_129, A_130]: (C_128=B_129 | ~r1_tarski(B_129, C_128) | ~v2_tex_2(C_128, A_130) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_130))) | ~v3_tex_2(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.44/6.94  tff(c_706, plain, (![A_7, A_130]: (A_7='#skF_4' | ~v2_tex_2(A_7, A_130) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_130))) | ~v3_tex_2('#skF_4', A_130) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_76, c_704])).
% 15.44/6.94  tff(c_710, plain, (![A_131, A_132]: (A_131='#skF_4' | ~v2_tex_2(A_131, A_132) | ~m1_subset_1(A_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~v3_tex_2('#skF_4', A_132) | ~l1_pre_topc(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_706])).
% 15.44/6.94  tff(c_737, plain, (![A_13, A_132]: (k1_tarski(A_13)='#skF_4' | ~v2_tex_2(k1_tarski(A_13), A_132) | ~v3_tex_2('#skF_4', A_132) | ~l1_pre_topc(A_132) | ~r2_hidden(A_13, u1_struct_0(A_132)))), inference(resolution, [status(thm)], [c_24, c_710])).
% 15.44/6.94  tff(c_754, plain, (![A_13, A_132]: (~v2_tex_2(k1_tarski(A_13), A_132) | ~v3_tex_2('#skF_4', A_132) | ~l1_pre_topc(A_132) | ~r2_hidden(A_13, u1_struct_0(A_132)))), inference(negUnitSimplification, [status(thm)], [c_106, c_737])).
% 15.44/6.94  tff(c_24265, plain, (![A_624]: (~v3_tex_2('#skF_4', A_624) | ~r2_hidden('#skF_1'(u1_struct_0(A_624)), u1_struct_0(A_624)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_624)), u1_struct_0(A_624)) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624) | v1_xboole_0(u1_struct_0(A_624)))), inference(resolution, [status(thm)], [c_2167, c_754])).
% 15.44/6.94  tff(c_24469, plain, (![A_627]: (~v3_tex_2('#skF_4', A_627) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627) | ~m1_subset_1('#skF_1'(u1_struct_0(A_627)), u1_struct_0(A_627)) | v1_xboole_0(u1_struct_0(A_627)))), inference(resolution, [status(thm)], [c_16, c_24265])).
% 15.44/6.94  tff(c_24483, plain, (![A_628]: (~v3_tex_2('#skF_4', A_628) | ~l1_pre_topc(A_628) | ~v2_pre_topc(A_628) | v2_struct_0(A_628) | v1_xboole_0(u1_struct_0(A_628)))), inference(resolution, [status(thm)], [c_144, c_24469])).
% 15.44/6.94  tff(c_30, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.44/6.94  tff(c_24496, plain, (![A_629]: (~l1_struct_0(A_629) | ~v3_tex_2('#skF_4', A_629) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(resolution, [status(thm)], [c_24483, c_30])).
% 15.44/6.94  tff(c_24506, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_24496])).
% 15.44/6.94  tff(c_24510, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_24506])).
% 15.44/6.94  tff(c_24511, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_24510])).
% 15.44/6.94  tff(c_24514, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_24511])).
% 15.44/6.94  tff(c_24518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_24514])).
% 15.44/6.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.44/6.94  
% 15.44/6.94  Inference rules
% 15.44/6.94  ----------------------
% 15.44/6.94  #Ref     : 0
% 15.44/6.94  #Sup     : 5754
% 15.44/6.94  #Fact    : 0
% 15.44/6.94  #Define  : 0
% 15.44/6.94  #Split   : 14
% 15.44/6.94  #Chain   : 0
% 15.44/6.94  #Close   : 0
% 15.44/6.94  
% 15.44/6.94  Ordering : KBO
% 15.44/6.94  
% 15.44/6.94  Simplification rules
% 15.44/6.94  ----------------------
% 15.44/6.94  #Subsume      : 1844
% 15.44/6.94  #Demod        : 3656
% 15.44/6.94  #Tautology    : 1441
% 15.44/6.94  #SimpNegUnit  : 1341
% 15.44/6.94  #BackRed      : 7
% 15.44/6.94  
% 15.44/6.94  #Partial instantiations: 0
% 15.44/6.94  #Strategies tried      : 1
% 15.44/6.94  
% 15.44/6.94  Timing (in seconds)
% 15.44/6.94  ----------------------
% 15.44/6.94  Preprocessing        : 0.31
% 15.44/6.94  Parsing              : 0.17
% 15.44/6.94  CNF conversion       : 0.02
% 15.44/6.94  Main loop            : 5.87
% 15.44/6.94  Inferencing          : 1.05
% 15.44/6.94  Reduction            : 1.29
% 15.44/6.94  Demodulation         : 0.82
% 15.44/6.94  BG Simplification    : 0.11
% 15.44/6.94  Subsumption          : 3.14
% 15.44/6.94  Abstraction          : 0.18
% 15.44/6.94  MUC search           : 0.00
% 15.44/6.94  Cooper               : 0.00
% 15.44/6.94  Total                : 6.21
% 15.44/6.94  Index Insertion      : 0.00
% 15.44/6.94  Index Deletion       : 0.00
% 15.44/6.94  Index Matching       : 0.00
% 15.44/6.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
