%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 156 expanded)
%              Number of leaves         :   33 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 322 expanded)
%              Number of equality atoms :   23 (  62 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

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

tff(f_41,axiom,(
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

tff(f_39,axiom,(
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

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_142,plain,(
    ! [A_71,B_72] :
      ( r1_tarski('#skF_2'(A_71,B_72),B_72)
      | v2_tex_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_153,plain,(
    ! [A_74] :
      ( r1_tarski('#skF_2'(A_74,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_50,c_142])).

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

tff(c_174,plain,(
    ! [A_77] :
      ( '#skF_2'(A_77,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_153,c_64])).

tff(c_177,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_32])).

tff(c_180,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_177])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_104,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tops_1(A_63,B_64),B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,(
    ! [A_67] :
      ( r1_tarski(k1_tops_1(A_67,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_123,plain,(
    ! [A_68] :
      ( k1_tops_1(A_68,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_118,c_64])).

tff(c_127,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_137,plain,(
    ! [A_69,B_70] :
      ( v3_pre_topc(k1_tops_1(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [A_73] :
      ( v3_pre_topc(k1_tops_1(A_73,'#skF_4'),A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_150,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_147])).

tff(c_152,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_150])).

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

tff(c_100,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_8,B_61] : k9_subset_1(A_8,B_61,'#skF_4') = k3_xboole_0(B_61,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_100])).

tff(c_250,plain,(
    ! [A_94,B_95,D_96] :
      ( k9_subset_1(u1_struct_0(A_94),B_95,D_96) != '#skF_2'(A_94,B_95)
      | ~ v3_pre_topc(D_96,A_94)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | v2_tex_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_253,plain,(
    ! [B_61,A_94] :
      ( k3_xboole_0(B_61,'#skF_4') != '#skF_2'(A_94,B_61)
      | ~ v3_pre_topc('#skF_4',A_94)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_94)))
      | v2_tex_2(B_61,A_94)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_250])).

tff(c_273,plain,(
    ! [B_99,A_100] :
      ( k3_xboole_0(B_99,'#skF_4') != '#skF_2'(A_100,B_99)
      | ~ v3_pre_topc('#skF_4',A_100)
      | v2_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_253])).

tff(c_280,plain,(
    ! [A_100] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_100,'#skF_4')
      | ~ v3_pre_topc('#skF_4',A_100)
      | v2_tex_2('#skF_4',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_50,c_273])).

tff(c_284,plain,(
    ! [A_101] :
      ( '#skF_2'(A_101,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_101)
      | v2_tex_2('#skF_4',A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_280])).

tff(c_287,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_152,c_284])).

tff(c_290,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_180,c_287])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.48  
% 2.40/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.48  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.40/1.48  
% 2.40/1.48  %Foreground sorts:
% 2.40/1.48  
% 2.40/1.48  
% 2.40/1.48  %Background operators:
% 2.40/1.48  
% 2.40/1.48  
% 2.40/1.48  %Foreground operators:
% 2.40/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.40/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.40/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.48  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.40/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.40/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.40/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.40/1.48  
% 2.54/1.50  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.54/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.54/1.50  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.54/1.50  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.54/1.50  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.54/1.50  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.54/1.50  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.54/1.50  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.54/1.50  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.54/1.50  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.54/1.50  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.54/1.50  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.54/1.50  tff(c_44, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.50  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.54/1.50  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.50  tff(c_50, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 2.54/1.50  tff(c_142, plain, (![A_71, B_72]: (r1_tarski('#skF_2'(A_71, B_72), B_72) | v2_tex_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.54/1.50  tff(c_153, plain, (![A_74]: (r1_tarski('#skF_2'(A_74, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_50, c_142])).
% 2.54/1.50  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.50  tff(c_64, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.54/1.50  tff(c_174, plain, (![A_77]: ('#skF_2'(A_77, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_153, c_64])).
% 2.54/1.50  tff(c_177, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_174, c_32])).
% 2.54/1.50  tff(c_180, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_177])).
% 2.54/1.50  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.54/1.50  tff(c_104, plain, (![A_63, B_64]: (r1_tarski(k1_tops_1(A_63, B_64), B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.54/1.50  tff(c_118, plain, (![A_67]: (r1_tarski(k1_tops_1(A_67, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_50, c_104])).
% 2.54/1.50  tff(c_123, plain, (![A_68]: (k1_tops_1(A_68, '#skF_4')='#skF_4' | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_118, c_64])).
% 2.54/1.50  tff(c_127, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.54/1.50  tff(c_137, plain, (![A_69, B_70]: (v3_pre_topc(k1_tops_1(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.50  tff(c_147, plain, (![A_73]: (v3_pre_topc(k1_tops_1(A_73, '#skF_4'), A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(resolution, [status(thm)], [c_50, c_137])).
% 2.54/1.50  tff(c_150, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_147])).
% 2.54/1.50  tff(c_152, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_150])).
% 2.54/1.50  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k3_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.50  tff(c_65, plain, (![A_51]: (A_51='#skF_4' | ~r1_tarski(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_6])).
% 2.54/1.50  tff(c_70, plain, (![B_3]: (k3_xboole_0('#skF_4', B_3)='#skF_4')), inference(resolution, [status(thm)], [c_4, c_65])).
% 2.54/1.50  tff(c_100, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.50  tff(c_103, plain, (![A_8, B_61]: (k9_subset_1(A_8, B_61, '#skF_4')=k3_xboole_0(B_61, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_100])).
% 2.54/1.50  tff(c_250, plain, (![A_94, B_95, D_96]: (k9_subset_1(u1_struct_0(A_94), B_95, D_96)!='#skF_2'(A_94, B_95) | ~v3_pre_topc(D_96, A_94) | ~m1_subset_1(D_96, k1_zfmisc_1(u1_struct_0(A_94))) | v2_tex_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.54/1.50  tff(c_253, plain, (![B_61, A_94]: (k3_xboole_0(B_61, '#skF_4')!='#skF_2'(A_94, B_61) | ~v3_pre_topc('#skF_4', A_94) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_94))) | v2_tex_2(B_61, A_94) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_103, c_250])).
% 2.54/1.50  tff(c_273, plain, (![B_99, A_100]: (k3_xboole_0(B_99, '#skF_4')!='#skF_2'(A_100, B_99) | ~v3_pre_topc('#skF_4', A_100) | v2_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_253])).
% 2.54/1.50  tff(c_280, plain, (![A_100]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_100, '#skF_4') | ~v3_pre_topc('#skF_4', A_100) | v2_tex_2('#skF_4', A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_50, c_273])).
% 2.54/1.50  tff(c_284, plain, (![A_101]: ('#skF_2'(A_101, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_101) | v2_tex_2('#skF_4', A_101) | ~l1_pre_topc(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_280])).
% 2.54/1.50  tff(c_287, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_152, c_284])).
% 2.54/1.50  tff(c_290, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_180, c_287])).
% 2.54/1.50  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_290])).
% 2.54/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.50  
% 2.54/1.50  Inference rules
% 2.54/1.50  ----------------------
% 2.54/1.50  #Ref     : 0
% 2.54/1.50  #Sup     : 53
% 2.54/1.50  #Fact    : 0
% 2.54/1.50  #Define  : 0
% 2.54/1.50  #Split   : 0
% 2.54/1.50  #Chain   : 0
% 2.54/1.50  #Close   : 0
% 2.54/1.50  
% 2.54/1.50  Ordering : KBO
% 2.54/1.50  
% 2.54/1.50  Simplification rules
% 2.54/1.50  ----------------------
% 2.54/1.50  #Subsume      : 1
% 2.54/1.50  #Demod        : 40
% 2.54/1.50  #Tautology    : 24
% 2.54/1.50  #SimpNegUnit  : 8
% 2.54/1.50  #BackRed      : 2
% 2.54/1.50  
% 2.54/1.50  #Partial instantiations: 0
% 2.54/1.50  #Strategies tried      : 1
% 2.54/1.50  
% 2.54/1.50  Timing (in seconds)
% 2.54/1.50  ----------------------
% 2.54/1.50  Preprocessing        : 0.43
% 2.54/1.50  Parsing              : 0.24
% 2.54/1.50  CNF conversion       : 0.03
% 2.54/1.50  Main loop            : 0.23
% 2.54/1.50  Inferencing          : 0.09
% 2.54/1.50  Reduction            : 0.07
% 2.54/1.50  Demodulation         : 0.05
% 2.54/1.50  BG Simplification    : 0.02
% 2.54/1.50  Subsumption          : 0.04
% 2.54/1.50  Abstraction          : 0.02
% 2.54/1.50  MUC search           : 0.00
% 2.54/1.50  Cooper               : 0.00
% 2.54/1.50  Total                : 0.69
% 2.54/1.50  Index Insertion      : 0.00
% 2.54/1.50  Index Deletion       : 0.00
% 2.54/1.50  Index Matching       : 0.00
% 2.54/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
