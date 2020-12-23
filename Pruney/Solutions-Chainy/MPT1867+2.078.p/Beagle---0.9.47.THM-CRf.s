%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:32 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 132 expanded)
%              Number of leaves         :   39 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 252 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_20] :
      ( v3_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_79,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_6,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_6])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_18])).

tff(c_263,plain,(
    ! [A_85,B_86] :
      ( r1_tarski('#skF_2'(A_85,B_86),B_86)
      | v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_294,plain,(
    ! [A_89] :
      ( r1_tarski('#skF_2'(A_89,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_87,c_263])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k2_xboole_0(A_2,B_3) = B_3
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_297,plain,(
    ! [A_89] :
      ( k2_xboole_0('#skF_2'(A_89,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_294,c_4])).

tff(c_300,plain,(
    ! [A_90] :
      ( '#skF_2'(A_90,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_297])).

tff(c_303,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_300,c_40])).

tff(c_306,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_303])).

tff(c_24,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_127,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_8])).

tff(c_141,plain,(
    ! [A_68,B_69,C_70] :
      ( k9_subset_1(A_68,B_69,C_70) = k3_xboole_0(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [A_14,B_69] : k9_subset_1(A_14,B_69,'#skF_4') = k3_xboole_0(B_69,'#skF_4') ),
    inference(resolution,[status(thm)],[c_87,c_141])).

tff(c_147,plain,(
    ! [A_14,B_69] : k9_subset_1(A_14,B_69,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_143])).

tff(c_176,plain,(
    ! [A_77,C_78,B_79] :
      ( k9_subset_1(A_77,C_78,B_79) = k9_subset_1(A_77,B_79,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [A_14,B_79] : k9_subset_1(A_14,B_79,'#skF_4') = k9_subset_1(A_14,'#skF_4',B_79) ),
    inference(resolution,[status(thm)],[c_87,c_176])).

tff(c_182,plain,(
    ! [A_14,B_79] : k9_subset_1(A_14,'#skF_4',B_79) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_178])).

tff(c_473,plain,(
    ! [A_108,B_109,D_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,D_110) != '#skF_2'(A_108,B_109)
      | ~ v3_pre_topc(D_110,A_108)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_479,plain,(
    ! [A_108,B_79] :
      ( '#skF_2'(A_108,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_79,A_108)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2('#skF_4',A_108)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_473])).

tff(c_505,plain,(
    ! [A_113,B_114] :
      ( '#skF_2'(A_113,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tex_2('#skF_4',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_479])).

tff(c_511,plain,(
    ! [B_114] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_505])).

tff(c_522,plain,(
    ! [B_114] :
      ( ~ v3_pre_topc(B_114,'#skF_3')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_306,c_511])).

tff(c_526,plain,(
    ! [B_115] :
      ( ~ v3_pre_topc(B_115,'#skF_3')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_522])).

tff(c_540,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_51,c_526])).

tff(c_543,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_540])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.38  
% 2.67/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.38  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.67/1.38  
% 2.67/1.38  %Foreground sorts:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Background operators:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Foreground operators:
% 2.67/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.67/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.67/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.67/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.67/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.67/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.38  
% 2.67/1.40  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.67/1.40  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.67/1.40  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.67/1.40  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.67/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.67/1.40  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.67/1.40  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.40  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.67/1.40  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.67/1.40  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.67/1.40  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.67/1.40  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.67/1.40  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.67/1.40  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.67/1.40  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.67/1.40  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.67/1.40  tff(c_26, plain, (![A_20]: (v3_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.40  tff(c_12, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.40  tff(c_14, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.40  tff(c_51, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.67/1.40  tff(c_40, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.67/1.40  tff(c_44, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.67/1.40  tff(c_79, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.40  tff(c_83, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_79])).
% 2.67/1.40  tff(c_6, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.40  tff(c_86, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_6])).
% 2.67/1.40  tff(c_18, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.40  tff(c_87, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_18])).
% 2.67/1.40  tff(c_263, plain, (![A_85, B_86]: (r1_tarski('#skF_2'(A_85, B_86), B_86) | v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.67/1.40  tff(c_294, plain, (![A_89]: (r1_tarski('#skF_2'(A_89, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_87, c_263])).
% 2.67/1.40  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, B_3)=B_3 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.40  tff(c_297, plain, (![A_89]: (k2_xboole_0('#skF_2'(A_89, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_294, c_4])).
% 2.67/1.40  tff(c_300, plain, (![A_90]: ('#skF_2'(A_90, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_90) | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_297])).
% 2.67/1.40  tff(c_303, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_300, c_40])).
% 2.67/1.40  tff(c_306, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_303])).
% 2.67/1.40  tff(c_24, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.67/1.40  tff(c_102, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.67/1.40  tff(c_123, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_24, c_102])).
% 2.67/1.40  tff(c_127, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_123])).
% 2.67/1.40  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.40  tff(c_85, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_8])).
% 2.67/1.40  tff(c_141, plain, (![A_68, B_69, C_70]: (k9_subset_1(A_68, B_69, C_70)=k3_xboole_0(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.40  tff(c_143, plain, (![A_14, B_69]: (k9_subset_1(A_14, B_69, '#skF_4')=k3_xboole_0(B_69, '#skF_4'))), inference(resolution, [status(thm)], [c_87, c_141])).
% 2.67/1.40  tff(c_147, plain, (![A_14, B_69]: (k9_subset_1(A_14, B_69, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_143])).
% 2.67/1.40  tff(c_176, plain, (![A_77, C_78, B_79]: (k9_subset_1(A_77, C_78, B_79)=k9_subset_1(A_77, B_79, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.40  tff(c_178, plain, (![A_14, B_79]: (k9_subset_1(A_14, B_79, '#skF_4')=k9_subset_1(A_14, '#skF_4', B_79))), inference(resolution, [status(thm)], [c_87, c_176])).
% 2.67/1.40  tff(c_182, plain, (![A_14, B_79]: (k9_subset_1(A_14, '#skF_4', B_79)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_178])).
% 2.67/1.40  tff(c_473, plain, (![A_108, B_109, D_110]: (k9_subset_1(u1_struct_0(A_108), B_109, D_110)!='#skF_2'(A_108, B_109) | ~v3_pre_topc(D_110, A_108) | ~m1_subset_1(D_110, k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.67/1.40  tff(c_479, plain, (![A_108, B_79]: ('#skF_2'(A_108, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_79, A_108) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2('#skF_4', A_108) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(superposition, [status(thm), theory('equality')], [c_182, c_473])).
% 2.67/1.40  tff(c_505, plain, (![A_113, B_114]: ('#skF_2'(A_113, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | v2_tex_2('#skF_4', A_113) | ~l1_pre_topc(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_479])).
% 2.67/1.40  tff(c_511, plain, (![B_114]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v3_pre_topc(B_114, '#skF_3') | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_505])).
% 2.67/1.40  tff(c_522, plain, (![B_114]: (~v3_pre_topc(B_114, '#skF_3') | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_306, c_511])).
% 2.67/1.40  tff(c_526, plain, (![B_115]: (~v3_pre_topc(B_115, '#skF_3') | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_522])).
% 2.67/1.40  tff(c_540, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_51, c_526])).
% 2.67/1.40  tff(c_543, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_540])).
% 2.67/1.40  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_543])).
% 2.67/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  Inference rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Ref     : 0
% 2.67/1.40  #Sup     : 107
% 2.67/1.40  #Fact    : 0
% 2.67/1.40  #Define  : 0
% 2.67/1.40  #Split   : 2
% 2.67/1.40  #Chain   : 0
% 2.67/1.40  #Close   : 0
% 2.67/1.40  
% 2.67/1.40  Ordering : KBO
% 2.67/1.40  
% 2.67/1.40  Simplification rules
% 2.67/1.40  ----------------------
% 2.67/1.40  #Subsume      : 5
% 2.67/1.40  #Demod        : 74
% 2.67/1.40  #Tautology    : 51
% 2.67/1.40  #SimpNegUnit  : 7
% 2.67/1.40  #BackRed      : 4
% 2.67/1.40  
% 2.67/1.40  #Partial instantiations: 0
% 2.67/1.40  #Strategies tried      : 1
% 2.67/1.40  
% 2.67/1.40  Timing (in seconds)
% 2.67/1.40  ----------------------
% 2.67/1.40  Preprocessing        : 0.30
% 2.67/1.40  Parsing              : 0.16
% 2.67/1.40  CNF conversion       : 0.02
% 2.67/1.40  Main loop            : 0.27
% 2.67/1.40  Inferencing          : 0.10
% 2.67/1.40  Reduction            : 0.09
% 2.67/1.40  Demodulation         : 0.06
% 2.67/1.40  BG Simplification    : 0.02
% 2.67/1.40  Subsumption          : 0.04
% 2.67/1.40  Abstraction          : 0.02
% 2.67/1.40  MUC search           : 0.00
% 2.67/1.40  Cooper               : 0.00
% 2.67/1.40  Total                : 0.60
% 2.67/1.40  Index Insertion      : 0.00
% 2.67/1.40  Index Deletion       : 0.00
% 2.67/1.40  Index Matching       : 0.00
% 2.67/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
