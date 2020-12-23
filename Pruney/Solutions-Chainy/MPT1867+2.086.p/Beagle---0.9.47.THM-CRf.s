%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 188 expanded)
%              Number of leaves         :   38 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 389 expanded)
%              Number of equality atoms :   31 (  84 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_88,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_117,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k4_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_53] :
      ( A_53 = '#skF_4'
      | ~ r1_tarski(A_53,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_6])).

tff(c_87,plain,(
    ! [B_3] : k4_xboole_0('#skF_4',B_3) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_127,plain,(
    ! [B_58] : k3_xboole_0('#skF_4',B_58) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_87])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16])).

tff(c_299,plain,(
    ! [A_81,B_82] :
      ( r1_tarski('#skF_2'(A_81,B_82),B_82)
      | v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_312,plain,(
    ! [A_83] :
      ( r1_tarski('#skF_2'(A_83,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_70,c_299])).

tff(c_81,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_6])).

tff(c_317,plain,(
    ! [A_84] :
      ( '#skF_2'(A_84,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_312,c_81])).

tff(c_320,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_317,c_38])).

tff(c_323,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_320])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_24,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_112,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_108])).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_177,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_182,plain,(
    ! [A_8,B_71] : k9_subset_1(A_8,B_71,A_8) = k3_xboole_0(B_71,A_8) ),
    inference(resolution,[status(thm)],[c_49,c_177])).

tff(c_780,plain,(
    ! [A_113,B_114,D_115] :
      ( k9_subset_1(u1_struct_0(A_113),B_114,D_115) != '#skF_2'(A_113,B_114)
      | ~ v3_pre_topc(D_115,A_113)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_786,plain,(
    ! [B_71,A_113] :
      ( k3_xboole_0(B_71,u1_struct_0(A_113)) != '#skF_2'(A_113,B_71)
      | ~ v3_pre_topc(u1_struct_0(A_113),A_113)
      | ~ m1_subset_1(u1_struct_0(A_113),k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tex_2(B_71,A_113)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_780])).

tff(c_869,plain,(
    ! [B_128,A_129] :
      ( k3_xboole_0(B_128,u1_struct_0(A_129)) != '#skF_2'(A_129,B_128)
      | ~ v3_pre_topc(u1_struct_0(A_129),A_129)
      | v2_tex_2(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_786])).

tff(c_871,plain,(
    ! [B_128] :
      ( k3_xboole_0(B_128,u1_struct_0('#skF_3')) != '#skF_2'('#skF_3',B_128)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
      | v2_tex_2(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_869])).

tff(c_873,plain,(
    ! [B_128] :
      ( k3_xboole_0(B_128,k2_struct_0('#skF_3')) != '#skF_2'('#skF_3',B_128)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
      | v2_tex_2(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_112,c_112,c_871])).

tff(c_874,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_873])).

tff(c_877,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_874])).

tff(c_881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_877])).

tff(c_895,plain,(
    ! [B_132] :
      ( k3_xboole_0(B_132,k2_struct_0('#skF_3')) != '#skF_2'('#skF_3',B_132)
      | v2_tex_2(B_132,'#skF_3')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_873])).

tff(c_906,plain,
    ( k3_xboole_0('#skF_4',k2_struct_0('#skF_3')) != '#skF_2'('#skF_3','#skF_4')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_895])).

tff(c_912,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_323,c_906])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.55  
% 3.33/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.55  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.33/1.55  
% 3.33/1.55  %Foreground sorts:
% 3.33/1.55  
% 3.33/1.55  
% 3.33/1.55  %Background operators:
% 3.33/1.55  
% 3.33/1.55  
% 3.33/1.55  %Foreground operators:
% 3.33/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.33/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.55  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.33/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.33/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.33/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.33/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.55  
% 3.33/1.57  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.33/1.57  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.33/1.57  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.33/1.57  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.33/1.57  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.33/1.57  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.33/1.57  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 3.33/1.57  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.33/1.57  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.33/1.57  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.33/1.57  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.33/1.57  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.33/1.57  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.33/1.57  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.57  tff(c_117, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.57  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k4_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.57  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.57  tff(c_60, plain, (![A_47]: (k1_xboole_0=A_47 | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.57  tff(c_64, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_60])).
% 3.33/1.57  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.57  tff(c_82, plain, (![A_53]: (A_53='#skF_4' | ~r1_tarski(A_53, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_6])).
% 3.33/1.57  tff(c_87, plain, (![B_3]: (k4_xboole_0('#skF_4', B_3)='#skF_4')), inference(resolution, [status(thm)], [c_4, c_82])).
% 3.33/1.57  tff(c_127, plain, (![B_58]: (k3_xboole_0('#skF_4', B_58)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_117, c_87])).
% 3.33/1.57  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.57  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.57  tff(c_70, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16])).
% 3.33/1.57  tff(c_299, plain, (![A_81, B_82]: (r1_tarski('#skF_2'(A_81, B_82), B_82) | v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.57  tff(c_312, plain, (![A_83]: (r1_tarski('#skF_2'(A_83, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_70, c_299])).
% 3.33/1.57  tff(c_81, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_6])).
% 3.33/1.57  tff(c_317, plain, (![A_84]: ('#skF_2'(A_84, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_312, c_81])).
% 3.33/1.57  tff(c_320, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_317, c_38])).
% 3.33/1.57  tff(c_323, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_320])).
% 3.33/1.57  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.57  tff(c_24, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.57  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.57  tff(c_88, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.57  tff(c_108, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_22, c_88])).
% 3.33/1.57  tff(c_112, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_108])).
% 3.33/1.57  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.57  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.57  tff(c_49, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.33/1.57  tff(c_177, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, C_72)=k3_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.57  tff(c_182, plain, (![A_8, B_71]: (k9_subset_1(A_8, B_71, A_8)=k3_xboole_0(B_71, A_8))), inference(resolution, [status(thm)], [c_49, c_177])).
% 3.33/1.57  tff(c_780, plain, (![A_113, B_114, D_115]: (k9_subset_1(u1_struct_0(A_113), B_114, D_115)!='#skF_2'(A_113, B_114) | ~v3_pre_topc(D_115, A_113) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_113))) | v2_tex_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.57  tff(c_786, plain, (![B_71, A_113]: (k3_xboole_0(B_71, u1_struct_0(A_113))!='#skF_2'(A_113, B_71) | ~v3_pre_topc(u1_struct_0(A_113), A_113) | ~m1_subset_1(u1_struct_0(A_113), k1_zfmisc_1(u1_struct_0(A_113))) | v2_tex_2(B_71, A_113) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(superposition, [status(thm), theory('equality')], [c_182, c_780])).
% 3.33/1.57  tff(c_869, plain, (![B_128, A_129]: (k3_xboole_0(B_128, u1_struct_0(A_129))!='#skF_2'(A_129, B_128) | ~v3_pre_topc(u1_struct_0(A_129), A_129) | v2_tex_2(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_786])).
% 3.33/1.57  tff(c_871, plain, (![B_128]: (k3_xboole_0(B_128, u1_struct_0('#skF_3'))!='#skF_2'('#skF_3', B_128) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | v2_tex_2(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_869])).
% 3.33/1.57  tff(c_873, plain, (![B_128]: (k3_xboole_0(B_128, k2_struct_0('#skF_3'))!='#skF_2'('#skF_3', B_128) | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | v2_tex_2(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_112, c_112, c_871])).
% 3.33/1.57  tff(c_874, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_873])).
% 3.33/1.57  tff(c_877, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_874])).
% 3.33/1.57  tff(c_881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_877])).
% 3.33/1.57  tff(c_895, plain, (![B_132]: (k3_xboole_0(B_132, k2_struct_0('#skF_3'))!='#skF_2'('#skF_3', B_132) | v2_tex_2(B_132, '#skF_3') | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_873])).
% 3.33/1.57  tff(c_906, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_3'))!='#skF_2'('#skF_3', '#skF_4') | v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_895])).
% 3.33/1.57  tff(c_912, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_323, c_906])).
% 3.33/1.57  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_912])).
% 3.33/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  
% 3.33/1.57  Inference rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Ref     : 0
% 3.33/1.57  #Sup     : 194
% 3.33/1.57  #Fact    : 0
% 3.33/1.57  #Define  : 0
% 3.33/1.57  #Split   : 4
% 3.33/1.57  #Chain   : 0
% 3.33/1.57  #Close   : 0
% 3.33/1.57  
% 3.33/1.57  Ordering : KBO
% 3.33/1.57  
% 3.33/1.57  Simplification rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Subsume      : 8
% 3.33/1.57  #Demod        : 219
% 3.33/1.57  #Tautology    : 107
% 3.33/1.57  #SimpNegUnit  : 8
% 3.33/1.57  #BackRed      : 1
% 3.33/1.57  
% 3.33/1.57  #Partial instantiations: 0
% 3.33/1.57  #Strategies tried      : 1
% 3.33/1.57  
% 3.33/1.57  Timing (in seconds)
% 3.33/1.57  ----------------------
% 3.43/1.57  Preprocessing        : 0.33
% 3.43/1.57  Parsing              : 0.17
% 3.43/1.57  CNF conversion       : 0.02
% 3.43/1.57  Main loop            : 0.46
% 3.43/1.57  Inferencing          : 0.17
% 3.43/1.57  Reduction            : 0.16
% 3.43/1.57  Demodulation         : 0.13
% 3.43/1.57  BG Simplification    : 0.02
% 3.43/1.57  Subsumption          : 0.07
% 3.43/1.57  Abstraction          : 0.03
% 3.43/1.57  MUC search           : 0.00
% 3.43/1.57  Cooper               : 0.00
% 3.43/1.57  Total                : 0.83
% 3.43/1.57  Index Insertion      : 0.00
% 3.43/1.57  Index Deletion       : 0.00
% 3.43/1.57  Index Matching       : 0.00
% 3.43/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
