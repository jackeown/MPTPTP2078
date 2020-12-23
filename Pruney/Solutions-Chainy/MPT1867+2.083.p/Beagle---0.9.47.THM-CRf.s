%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 154 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 305 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_93,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_61,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72,plain,(
    ! [A_13] : m1_subset_1('#skF_5',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_16])).

tff(c_218,plain,(
    ! [A_78,B_79] :
      ( r1_tarski('#skF_3'(A_78,B_79),B_79)
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_302,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_3'(A_85,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_72,c_218])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_4] :
      ( A_4 = '#skF_5'
      | ~ r1_tarski(A_4,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_6])).

tff(c_320,plain,(
    ! [A_88] :
      ( '#skF_3'(A_88,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_302,c_82])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_323,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_320,c_40])).

tff(c_326,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323])).

tff(c_22,plain,(
    ! [A_17] :
      ( v3_pre_topc('#skF_1'(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_17] :
      ( m1_subset_1('#skF_1'(A_17),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k3_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_52] :
      ( A_52 = '#skF_5'
      | ~ r1_tarski(A_52,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_6])).

tff(c_88,plain,(
    ! [B_3] : k3_xboole_0('#skF_5',B_3) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_10,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_116,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [A_9,B_65] : k9_subset_1(A_9,B_65,A_9) = k3_xboole_0(B_65,A_9) ),
    inference(resolution,[status(thm)],[c_51,c_116])).

tff(c_158,plain,(
    ! [A_72,C_73,B_74] :
      ( k9_subset_1(A_72,C_73,B_74) = k9_subset_1(A_72,B_74,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [A_9,B_74] : k9_subset_1(A_9,B_74,A_9) = k9_subset_1(A_9,A_9,B_74) ),
    inference(resolution,[status(thm)],[c_51,c_158])).

tff(c_170,plain,(
    ! [A_75,B_76] : k9_subset_1(A_75,A_75,B_76) = k3_xboole_0(B_76,A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_164])).

tff(c_121,plain,(
    ! [A_13,B_65] : k9_subset_1(A_13,B_65,'#skF_5') = k3_xboole_0(B_65,'#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_116])).

tff(c_177,plain,(
    ! [A_75] : k3_xboole_0(A_75,'#skF_5') = k3_xboole_0('#skF_5',A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_121])).

tff(c_194,plain,(
    ! [A_75] : k3_xboole_0(A_75,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_177])).

tff(c_162,plain,(
    ! [A_13,B_74] : k9_subset_1(A_13,B_74,'#skF_5') = k9_subset_1(A_13,'#skF_5',B_74) ),
    inference(resolution,[status(thm)],[c_72,c_158])).

tff(c_167,plain,(
    ! [A_13,B_74] : k9_subset_1(A_13,'#skF_5',B_74) = k3_xboole_0(B_74,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_162])).

tff(c_266,plain,(
    ! [A_13,B_74] : k9_subset_1(A_13,'#skF_5',B_74) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_167])).

tff(c_402,plain,(
    ! [A_99,B_100,D_101] :
      ( k9_subset_1(u1_struct_0(A_99),B_100,D_101) != '#skF_3'(A_99,B_100)
      | ~ v3_pre_topc(D_101,A_99)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(u1_struct_0(A_99)))
      | v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_407,plain,(
    ! [A_99,B_74] :
      ( '#skF_3'(A_99,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc(B_74,A_99)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_99)))
      | v2_tex_2('#skF_5',A_99)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_402])).

tff(c_487,plain,(
    ! [A_114,B_115] :
      ( '#skF_3'(A_114,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | v2_tex_2('#skF_5',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_407])).

tff(c_531,plain,(
    ! [A_120] :
      ( '#skF_3'(A_120,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_1'(A_120),A_120)
      | v2_tex_2('#skF_5',A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_26,c_487])).

tff(c_536,plain,(
    ! [A_121] :
      ( '#skF_3'(A_121,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_22,c_531])).

tff(c_539,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_536,c_40])).

tff(c_542,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_326,c_539])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.89  
% 3.32/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.89  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.32/1.89  
% 3.32/1.89  %Foreground sorts:
% 3.32/1.89  
% 3.32/1.89  
% 3.32/1.89  %Background operators:
% 3.32/1.89  
% 3.32/1.89  
% 3.32/1.89  %Foreground operators:
% 3.32/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.32/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.32/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.89  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.89  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.32/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.32/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.32/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.89  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.32/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.32/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.89  
% 3.57/1.92  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.57/1.92  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.57/1.92  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.57/1.92  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 3.57/1.92  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.57/1.92  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.57/1.92  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.57/1.92  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.57/1.92  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.57/1.92  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.57/1.92  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.57/1.92  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.57/1.92  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.57/1.92  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.57/1.92  tff(c_44, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.57/1.92  tff(c_61, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.92  tff(c_65, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_61])).
% 3.57/1.92  tff(c_16, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.92  tff(c_72, plain, (![A_13]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_16])).
% 3.57/1.92  tff(c_218, plain, (![A_78, B_79]: (r1_tarski('#skF_3'(A_78, B_79), B_79) | v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.92  tff(c_302, plain, (![A_85]: (r1_tarski('#skF_3'(A_85, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_72, c_218])).
% 3.57/1.92  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.92  tff(c_82, plain, (![A_4]: (A_4='#skF_5' | ~r1_tarski(A_4, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_6])).
% 3.57/1.92  tff(c_320, plain, (![A_88]: ('#skF_3'(A_88, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_302, c_82])).
% 3.57/1.92  tff(c_40, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.57/1.92  tff(c_323, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_320, c_40])).
% 3.57/1.92  tff(c_326, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323])).
% 3.57/1.92  tff(c_22, plain, (![A_17]: (v3_pre_topc('#skF_1'(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.57/1.92  tff(c_26, plain, (![A_17]: (m1_subset_1('#skF_1'(A_17), k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.57/1.92  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k3_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.92  tff(c_83, plain, (![A_52]: (A_52='#skF_5' | ~r1_tarski(A_52, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_6])).
% 3.57/1.92  tff(c_88, plain, (![B_3]: (k3_xboole_0('#skF_5', B_3)='#skF_5')), inference(resolution, [status(thm)], [c_4, c_83])).
% 3.57/1.92  tff(c_10, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.92  tff(c_12, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.92  tff(c_51, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.57/1.92  tff(c_116, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.92  tff(c_122, plain, (![A_9, B_65]: (k9_subset_1(A_9, B_65, A_9)=k3_xboole_0(B_65, A_9))), inference(resolution, [status(thm)], [c_51, c_116])).
% 3.57/1.92  tff(c_158, plain, (![A_72, C_73, B_74]: (k9_subset_1(A_72, C_73, B_74)=k9_subset_1(A_72, B_74, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.92  tff(c_164, plain, (![A_9, B_74]: (k9_subset_1(A_9, B_74, A_9)=k9_subset_1(A_9, A_9, B_74))), inference(resolution, [status(thm)], [c_51, c_158])).
% 3.57/1.92  tff(c_170, plain, (![A_75, B_76]: (k9_subset_1(A_75, A_75, B_76)=k3_xboole_0(B_76, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_164])).
% 3.57/1.92  tff(c_121, plain, (![A_13, B_65]: (k9_subset_1(A_13, B_65, '#skF_5')=k3_xboole_0(B_65, '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_116])).
% 3.57/1.92  tff(c_177, plain, (![A_75]: (k3_xboole_0(A_75, '#skF_5')=k3_xboole_0('#skF_5', A_75))), inference(superposition, [status(thm), theory('equality')], [c_170, c_121])).
% 3.57/1.92  tff(c_194, plain, (![A_75]: (k3_xboole_0(A_75, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_177])).
% 3.57/1.92  tff(c_162, plain, (![A_13, B_74]: (k9_subset_1(A_13, B_74, '#skF_5')=k9_subset_1(A_13, '#skF_5', B_74))), inference(resolution, [status(thm)], [c_72, c_158])).
% 3.57/1.92  tff(c_167, plain, (![A_13, B_74]: (k9_subset_1(A_13, '#skF_5', B_74)=k3_xboole_0(B_74, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_162])).
% 3.57/1.92  tff(c_266, plain, (![A_13, B_74]: (k9_subset_1(A_13, '#skF_5', B_74)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_167])).
% 3.57/1.92  tff(c_402, plain, (![A_99, B_100, D_101]: (k9_subset_1(u1_struct_0(A_99), B_100, D_101)!='#skF_3'(A_99, B_100) | ~v3_pre_topc(D_101, A_99) | ~m1_subset_1(D_101, k1_zfmisc_1(u1_struct_0(A_99))) | v2_tex_2(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.92  tff(c_407, plain, (![A_99, B_74]: ('#skF_3'(A_99, '#skF_5')!='#skF_5' | ~v3_pre_topc(B_74, A_99) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_99))) | v2_tex_2('#skF_5', A_99) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(superposition, [status(thm), theory('equality')], [c_266, c_402])).
% 3.57/1.92  tff(c_487, plain, (![A_114, B_115]: ('#skF_3'(A_114, '#skF_5')!='#skF_5' | ~v3_pre_topc(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | v2_tex_2('#skF_5', A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_407])).
% 3.57/1.92  tff(c_531, plain, (![A_120]: ('#skF_3'(A_120, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_1'(A_120), A_120) | v2_tex_2('#skF_5', A_120) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_26, c_487])).
% 3.57/1.92  tff(c_536, plain, (![A_121]: ('#skF_3'(A_121, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_22, c_531])).
% 3.57/1.92  tff(c_539, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_536, c_40])).
% 3.57/1.92  tff(c_542, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_326, c_539])).
% 3.57/1.92  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_542])).
% 3.57/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.92  
% 3.57/1.92  Inference rules
% 3.57/1.92  ----------------------
% 3.57/1.92  #Ref     : 0
% 3.57/1.92  #Sup     : 110
% 3.57/1.92  #Fact    : 0
% 3.57/1.92  #Define  : 0
% 3.57/1.92  #Split   : 0
% 3.57/1.92  #Chain   : 0
% 3.57/1.92  #Close   : 0
% 3.57/1.92  
% 3.57/1.92  Ordering : KBO
% 3.57/1.92  
% 3.57/1.92  Simplification rules
% 3.57/1.92  ----------------------
% 3.57/1.92  #Subsume      : 3
% 3.57/1.92  #Demod        : 39
% 3.57/1.92  #Tautology    : 50
% 3.57/1.92  #SimpNegUnit  : 3
% 3.57/1.92  #BackRed      : 2
% 3.57/1.92  
% 3.57/1.92  #Partial instantiations: 0
% 3.57/1.92  #Strategies tried      : 1
% 3.57/1.92  
% 3.57/1.92  Timing (in seconds)
% 3.57/1.92  ----------------------
% 3.57/1.93  Preprocessing        : 0.51
% 3.57/1.93  Parsing              : 0.26
% 3.57/1.93  CNF conversion       : 0.04
% 3.57/1.93  Main loop            : 0.48
% 3.57/1.93  Inferencing          : 0.18
% 3.57/1.93  Reduction            : 0.15
% 3.57/1.93  Demodulation         : 0.11
% 3.57/1.93  BG Simplification    : 0.03
% 3.57/1.93  Subsumption          : 0.09
% 3.57/1.93  Abstraction          : 0.03
% 3.57/1.93  MUC search           : 0.00
% 3.57/1.93  Cooper               : 0.00
% 3.57/1.93  Total                : 1.05
% 3.57/1.93  Index Insertion      : 0.00
% 3.57/1.93  Index Deletion       : 0.00
% 3.57/1.93  Index Matching       : 0.00
% 3.57/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
