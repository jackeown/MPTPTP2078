%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 155 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 322 expanded)
%              Number of equality atoms :   23 (  62 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_255,plain,(
    ! [A_78,B_79] :
      ( r1_tarski('#skF_2'(A_78,B_79),B_79)
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_260,plain,(
    ! [A_80] :
      ( r1_tarski('#skF_2'(A_80,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_50,c_255])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_6])).

tff(c_281,plain,(
    ! [A_83] :
      ( '#skF_2'(A_83,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_260,c_64])).

tff(c_284,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_281,c_32])).

tff(c_287,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_284])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_144,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_tops_1(A_67,B_68),B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_149,plain,(
    ! [A_69] :
      ( r1_tarski(k1_tops_1(A_69,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_50,c_144])).

tff(c_159,plain,(
    ! [A_72] :
      ( k1_tops_1(A_72,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_149,c_64])).

tff(c_163,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_159])).

tff(c_154,plain,(
    ! [A_70,B_71] :
      ( v3_pre_topc(k1_tops_1(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_173,plain,(
    ! [A_73] :
      ( v3_pre_topc(k1_tops_1(A_73,'#skF_4'),A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_50,c_154])).

tff(c_176,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_173])).

tff(c_178,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_176])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k3_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_51] :
      ( A_51 = '#skF_4'
      | ~ r1_tarski(A_51,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_6])).

tff(c_70,plain,(
    ! [B_3] : k3_xboole_0('#skF_4',B_3) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_122,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [A_10,B_63] : k9_subset_1(A_10,B_63,'#skF_4') = k3_xboole_0(B_63,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_476,plain,(
    ! [A_101,B_102,D_103] :
      ( k9_subset_1(u1_struct_0(A_101),B_102,D_103) != '#skF_2'(A_101,B_102)
      | ~ v3_pre_topc(D_103,A_101)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(A_101)))
      | v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_479,plain,(
    ! [B_63,A_101] :
      ( k3_xboole_0(B_63,'#skF_4') != '#skF_2'(A_101,B_63)
      | ~ v3_pre_topc('#skF_4',A_101)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_101)))
      | v2_tex_2(B_63,A_101)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_476])).

tff(c_496,plain,(
    ! [B_107,A_108] :
      ( k3_xboole_0(B_107,'#skF_4') != '#skF_2'(A_108,B_107)
      | ~ v3_pre_topc('#skF_4',A_108)
      | v2_tex_2(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_479])).

tff(c_506,plain,(
    ! [A_108] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_108,'#skF_4')
      | ~ v3_pre_topc('#skF_4',A_108)
      | v2_tex_2('#skF_4',A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_50,c_496])).

tff(c_511,plain,(
    ! [A_109] :
      ( '#skF_2'(A_109,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_109)
      | v2_tex_2('#skF_4',A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_506])).

tff(c_514,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_511])).

tff(c_517,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_287,c_514])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.55  
% 2.65/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.55  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.65/1.55  
% 2.65/1.55  %Foreground sorts:
% 2.65/1.55  
% 2.65/1.55  
% 2.65/1.55  %Background operators:
% 2.65/1.55  
% 2.65/1.55  
% 2.65/1.55  %Foreground operators:
% 2.65/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.65/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.55  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.65/1.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.65/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.55  
% 2.65/1.57  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.65/1.57  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.65/1.57  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.65/1.57  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.65/1.57  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.65/1.57  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.65/1.57  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.65/1.57  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.65/1.57  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.65/1.57  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.57  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.57  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.57  tff(c_44, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.57  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.65/1.57  tff(c_12, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.57  tff(c_50, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 2.65/1.57  tff(c_255, plain, (![A_78, B_79]: (r1_tarski('#skF_2'(A_78, B_79), B_79) | v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.57  tff(c_260, plain, (![A_80]: (r1_tarski('#skF_2'(A_80, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_50, c_255])).
% 2.65/1.57  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.57  tff(c_64, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.65/1.57  tff(c_281, plain, (![A_83]: ('#skF_2'(A_83, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_260, c_64])).
% 2.65/1.57  tff(c_284, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_281, c_32])).
% 2.65/1.57  tff(c_287, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_284])).
% 2.65/1.57  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.57  tff(c_144, plain, (![A_67, B_68]: (r1_tarski(k1_tops_1(A_67, B_68), B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.57  tff(c_149, plain, (![A_69]: (r1_tarski(k1_tops_1(A_69, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_50, c_144])).
% 2.65/1.57  tff(c_159, plain, (![A_72]: (k1_tops_1(A_72, '#skF_4')='#skF_4' | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_149, c_64])).
% 2.65/1.57  tff(c_163, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_159])).
% 2.65/1.57  tff(c_154, plain, (![A_70, B_71]: (v3_pre_topc(k1_tops_1(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.57  tff(c_173, plain, (![A_73]: (v3_pre_topc(k1_tops_1(A_73, '#skF_4'), A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(resolution, [status(thm)], [c_50, c_154])).
% 2.65/1.57  tff(c_176, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_173])).
% 2.65/1.57  tff(c_178, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_176])).
% 2.65/1.57  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k3_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.57  tff(c_65, plain, (![A_51]: (A_51='#skF_4' | ~r1_tarski(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.65/1.57  tff(c_70, plain, (![B_3]: (k3_xboole_0('#skF_4', B_3)='#skF_4')), inference(resolution, [status(thm)], [c_4, c_65])).
% 2.65/1.57  tff(c_122, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.57  tff(c_125, plain, (![A_10, B_63]: (k9_subset_1(A_10, B_63, '#skF_4')=k3_xboole_0(B_63, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_122])).
% 2.65/1.57  tff(c_476, plain, (![A_101, B_102, D_103]: (k9_subset_1(u1_struct_0(A_101), B_102, D_103)!='#skF_2'(A_101, B_102) | ~v3_pre_topc(D_103, A_101) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(A_101))) | v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.57  tff(c_479, plain, (![B_63, A_101]: (k3_xboole_0(B_63, '#skF_4')!='#skF_2'(A_101, B_63) | ~v3_pre_topc('#skF_4', A_101) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_101))) | v2_tex_2(B_63, A_101) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(superposition, [status(thm), theory('equality')], [c_125, c_476])).
% 2.65/1.57  tff(c_496, plain, (![B_107, A_108]: (k3_xboole_0(B_107, '#skF_4')!='#skF_2'(A_108, B_107) | ~v3_pre_topc('#skF_4', A_108) | v2_tex_2(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_479])).
% 2.65/1.57  tff(c_506, plain, (![A_108]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_108, '#skF_4') | ~v3_pre_topc('#skF_4', A_108) | v2_tex_2('#skF_4', A_108) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_50, c_496])).
% 2.65/1.57  tff(c_511, plain, (![A_109]: ('#skF_2'(A_109, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_109) | v2_tex_2('#skF_4', A_109) | ~l1_pre_topc(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_506])).
% 2.65/1.57  tff(c_514, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_178, c_511])).
% 2.65/1.57  tff(c_517, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_287, c_514])).
% 2.65/1.57  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_517])).
% 2.65/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.57  
% 2.65/1.57  Inference rules
% 2.65/1.57  ----------------------
% 2.65/1.57  #Ref     : 0
% 2.65/1.57  #Sup     : 112
% 2.65/1.57  #Fact    : 0
% 2.65/1.57  #Define  : 0
% 2.65/1.57  #Split   : 0
% 2.65/1.57  #Chain   : 0
% 2.65/1.57  #Close   : 0
% 2.65/1.57  
% 2.65/1.57  Ordering : KBO
% 2.65/1.57  
% 2.65/1.57  Simplification rules
% 2.65/1.57  ----------------------
% 2.65/1.57  #Subsume      : 1
% 2.65/1.57  #Demod        : 106
% 2.65/1.57  #Tautology    : 62
% 2.65/1.57  #SimpNegUnit  : 7
% 2.65/1.57  #BackRed      : 2
% 2.65/1.57  
% 2.65/1.57  #Partial instantiations: 0
% 2.65/1.57  #Strategies tried      : 1
% 2.65/1.57  
% 2.65/1.57  Timing (in seconds)
% 2.65/1.57  ----------------------
% 2.65/1.57  Preprocessing        : 0.39
% 2.65/1.57  Parsing              : 0.23
% 2.65/1.57  CNF conversion       : 0.02
% 2.65/1.57  Main loop            : 0.27
% 2.65/1.57  Inferencing          : 0.11
% 2.65/1.57  Reduction            : 0.09
% 2.65/1.57  Demodulation         : 0.07
% 2.65/1.57  BG Simplification    : 0.02
% 2.65/1.57  Subsumption          : 0.04
% 2.65/1.57  Abstraction          : 0.02
% 2.65/1.57  MUC search           : 0.00
% 2.65/1.57  Cooper               : 0.00
% 2.65/1.57  Total                : 0.69
% 2.65/1.57  Index Insertion      : 0.00
% 2.65/1.57  Index Deletion       : 0.00
% 2.65/1.57  Index Matching       : 0.00
% 2.65/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
