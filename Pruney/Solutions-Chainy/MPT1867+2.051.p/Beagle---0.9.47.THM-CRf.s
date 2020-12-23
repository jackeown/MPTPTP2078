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
% DateTime   : Thu Dec  3 10:29:29 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 120 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 257 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_100,axiom,(
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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_392,plain,(
    ! [A_100,B_101] :
      ( r1_tarski('#skF_3'(A_100,B_101),B_101)
      | v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_397,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_392])).

tff(c_401,plain,
    ( r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_397])).

tff(c_402,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_401])).

tff(c_55,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_212,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_226,plain,(
    ! [B_74,A_75,A_76] :
      ( ~ v1_xboole_0(B_74)
      | ~ r2_hidden(A_75,A_76)
      | ~ r1_tarski(A_76,B_74) ) ),
    inference(resolution,[status(thm)],[c_24,c_212])).

tff(c_229,plain,(
    ! [B_74,A_2] :
      ( ~ v1_xboole_0(B_74)
      | ~ r1_tarski(A_2,B_74)
      | A_2 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_71,c_226])).

tff(c_410,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_402,c_229])).

tff(c_423,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_410])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_326,plain,(
    ! [B_91,A_92] :
      ( v4_pre_topc(B_91,A_92)
      | ~ v1_xboole_0(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_333,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_337,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_333])).

tff(c_10,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = '#skF_5'
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_14])).

tff(c_78,plain,(
    ! [B_5] : k4_xboole_0(B_5,B_5) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_110,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [B_5] : k3_xboole_0(B_5,B_5) = B_5 ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_136,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,(
    ! [B_5] : k4_xboole_0(B_5,'#skF_5') = k3_xboole_0(B_5,B_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_136])).

tff(c_159,plain,(
    ! [B_67] : k4_xboole_0(B_67,'#skF_5') = B_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_154])).

tff(c_18,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_165,plain,(
    ! [B_67] : k4_xboole_0(B_67,B_67) = k3_xboole_0(B_67,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_18])).

tff(c_178,plain,(
    ! [B_67] : k3_xboole_0(B_67,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_165])).

tff(c_266,plain,(
    ! [A_83,B_84,C_85] :
      ( k9_subset_1(A_83,B_84,C_85) = k3_xboole_0(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_270,plain,(
    ! [B_84] : k9_subset_1(u1_struct_0('#skF_4'),B_84,'#skF_5') = k3_xboole_0(B_84,'#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_266])).

tff(c_273,plain,(
    ! [B_84] : k9_subset_1(u1_struct_0('#skF_4'),B_84,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_270])).

tff(c_895,plain,(
    ! [A_126,B_127,D_128] :
      ( k9_subset_1(u1_struct_0(A_126),B_127,D_128) != '#skF_3'(A_126,B_127)
      | ~ v4_pre_topc(D_128,A_126)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_903,plain,(
    ! [B_84] :
      ( '#skF_3'('#skF_4',B_84) != '#skF_5'
      | ~ v4_pre_topc('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_84,'#skF_4')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_895])).

tff(c_906,plain,(
    ! [B_129] :
      ( '#skF_3'('#skF_4',B_129) != '#skF_5'
      | v2_tex_2(B_129,'#skF_4')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_337,c_903])).

tff(c_917,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_906])).

tff(c_924,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_917])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n005.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 15:18:02 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.31  
% 2.89/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.32  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.89/1.32  
% 2.89/1.32  %Foreground sorts:
% 2.89/1.32  
% 2.89/1.32  
% 2.89/1.32  %Background operators:
% 2.89/1.32  
% 2.89/1.32  
% 2.89/1.32  %Foreground operators:
% 2.89/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.89/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.89/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.89/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.89/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.89/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.32  
% 2.89/1.33  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.89/1.33  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.89/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.89/1.33  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.89/1.33  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.33  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.89/1.33  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.89/1.33  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.89/1.33  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.89/1.33  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.89/1.33  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.89/1.33  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.89/1.33  tff(c_42, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.33  tff(c_46, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.33  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.33  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.33  tff(c_392, plain, (![A_100, B_101]: (r1_tarski('#skF_3'(A_100, B_101), B_101) | v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.89/1.33  tff(c_397, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_44, c_392])).
% 2.89/1.33  tff(c_401, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_397])).
% 2.89/1.33  tff(c_402, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_401])).
% 2.89/1.33  tff(c_55, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.33  tff(c_59, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_55])).
% 2.89/1.33  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.33  tff(c_71, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_4])).
% 2.89/1.33  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.33  tff(c_212, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.89/1.33  tff(c_226, plain, (![B_74, A_75, A_76]: (~v1_xboole_0(B_74) | ~r2_hidden(A_75, A_76) | ~r1_tarski(A_76, B_74))), inference(resolution, [status(thm)], [c_24, c_212])).
% 2.89/1.33  tff(c_229, plain, (![B_74, A_2]: (~v1_xboole_0(B_74) | ~r1_tarski(A_2, B_74) | A_2='#skF_5')), inference(resolution, [status(thm)], [c_71, c_226])).
% 2.89/1.33  tff(c_410, plain, (~v1_xboole_0('#skF_5') | '#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_402, c_229])).
% 2.89/1.33  tff(c_423, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_410])).
% 2.89/1.33  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.33  tff(c_326, plain, (![B_91, A_92]: (v4_pre_topc(B_91, A_92) | ~v1_xboole_0(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.89/1.33  tff(c_333, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_44, c_326])).
% 2.89/1.33  tff(c_337, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_333])).
% 2.89/1.33  tff(c_10, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.33  tff(c_14, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.33  tff(c_74, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)='#skF_5' | ~r1_tarski(A_53, B_54))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_14])).
% 2.89/1.33  tff(c_78, plain, (![B_5]: (k4_xboole_0(B_5, B_5)='#skF_5')), inference(resolution, [status(thm)], [c_10, c_74])).
% 2.89/1.33  tff(c_110, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.33  tff(c_122, plain, (![B_5]: (k3_xboole_0(B_5, B_5)=B_5)), inference(resolution, [status(thm)], [c_10, c_110])).
% 2.89/1.33  tff(c_136, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.33  tff(c_154, plain, (![B_5]: (k4_xboole_0(B_5, '#skF_5')=k3_xboole_0(B_5, B_5))), inference(superposition, [status(thm), theory('equality')], [c_78, c_136])).
% 2.89/1.33  tff(c_159, plain, (![B_67]: (k4_xboole_0(B_67, '#skF_5')=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_154])).
% 2.89/1.33  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.33  tff(c_165, plain, (![B_67]: (k4_xboole_0(B_67, B_67)=k3_xboole_0(B_67, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_18])).
% 2.89/1.33  tff(c_178, plain, (![B_67]: (k3_xboole_0(B_67, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_165])).
% 2.89/1.33  tff(c_266, plain, (![A_83, B_84, C_85]: (k9_subset_1(A_83, B_84, C_85)=k3_xboole_0(B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.89/1.33  tff(c_270, plain, (![B_84]: (k9_subset_1(u1_struct_0('#skF_4'), B_84, '#skF_5')=k3_xboole_0(B_84, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_266])).
% 2.89/1.33  tff(c_273, plain, (![B_84]: (k9_subset_1(u1_struct_0('#skF_4'), B_84, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_270])).
% 2.89/1.33  tff(c_895, plain, (![A_126, B_127, D_128]: (k9_subset_1(u1_struct_0(A_126), B_127, D_128)!='#skF_3'(A_126, B_127) | ~v4_pre_topc(D_128, A_126) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0(A_126))) | v2_tex_2(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.89/1.33  tff(c_903, plain, (![B_84]: ('#skF_3'('#skF_4', B_84)!='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_84, '#skF_4') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_895])).
% 2.89/1.33  tff(c_906, plain, (![B_129]: ('#skF_3'('#skF_4', B_129)!='#skF_5' | v2_tex_2(B_129, '#skF_4') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_337, c_903])).
% 2.89/1.33  tff(c_917, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_906])).
% 2.89/1.33  tff(c_924, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_423, c_917])).
% 2.89/1.33  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_924])).
% 2.89/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.33  
% 2.89/1.33  Inference rules
% 2.89/1.33  ----------------------
% 2.89/1.33  #Ref     : 0
% 2.89/1.33  #Sup     : 206
% 2.89/1.33  #Fact    : 0
% 2.89/1.33  #Define  : 0
% 2.89/1.33  #Split   : 2
% 2.89/1.33  #Chain   : 0
% 2.89/1.33  #Close   : 0
% 2.89/1.33  
% 2.89/1.33  Ordering : KBO
% 2.89/1.33  
% 2.89/1.33  Simplification rules
% 2.89/1.33  ----------------------
% 2.89/1.33  #Subsume      : 10
% 2.89/1.33  #Demod        : 177
% 2.89/1.33  #Tautology    : 125
% 2.89/1.33  #SimpNegUnit  : 5
% 2.89/1.33  #BackRed      : 2
% 2.89/1.33  
% 2.89/1.33  #Partial instantiations: 0
% 2.89/1.33  #Strategies tried      : 1
% 2.89/1.33  
% 2.89/1.33  Timing (in seconds)
% 2.89/1.33  ----------------------
% 2.89/1.34  Preprocessing        : 0.31
% 2.89/1.34  Parsing              : 0.16
% 2.89/1.34  CNF conversion       : 0.02
% 2.89/1.34  Main loop            : 0.36
% 2.89/1.34  Inferencing          : 0.13
% 2.89/1.34  Reduction            : 0.12
% 2.89/1.34  Demodulation         : 0.09
% 2.89/1.34  BG Simplification    : 0.02
% 2.89/1.34  Subsumption          : 0.06
% 2.89/1.34  Abstraction          : 0.02
% 2.89/1.34  MUC search           : 0.00
% 2.89/1.34  Cooper               : 0.00
% 2.89/1.34  Total                : 0.70
% 2.89/1.34  Index Insertion      : 0.00
% 2.89/1.34  Index Deletion       : 0.00
% 2.89/1.34  Index Matching       : 0.00
% 2.89/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
