%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:32 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 134 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 260 expanded)
%              Number of equality atoms :   31 (  53 expanded)
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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_94,axiom,(
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

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [A_21] :
      ( v3_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_53,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_342,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),B_89)
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_356,plain,(
    ! [A_90] :
      ( r1_tarski('#skF_2'(A_90,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_92,c_342])).

tff(c_8,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_8])).

tff(c_361,plain,(
    ! [A_91] :
      ( '#skF_2'(A_91,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_356,c_102])).

tff(c_364,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_42])).

tff(c_367,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_364])).

tff(c_26,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_104,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_109,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_26,c_104])).

tff(c_113,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_4,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_2] : k3_xboole_0(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_4])).

tff(c_186,plain,(
    ! [A_69,B_70,C_71] :
      ( k9_subset_1(A_69,B_70,C_71) = k3_xboole_0(B_70,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,(
    ! [A_15,B_70] : k9_subset_1(A_15,B_70,'#skF_4') = k3_xboole_0(B_70,'#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_186])).

tff(c_193,plain,(
    ! [A_15,B_70] : k9_subset_1(A_15,B_70,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_190])).

tff(c_221,plain,(
    ! [A_78,C_79,B_80] :
      ( k9_subset_1(A_78,C_79,B_80) = k9_subset_1(A_78,B_80,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [A_15,B_80] : k9_subset_1(A_15,B_80,'#skF_4') = k9_subset_1(A_15,'#skF_4',B_80) ),
    inference(resolution,[status(thm)],[c_92,c_221])).

tff(c_229,plain,(
    ! [A_15,B_80] : k9_subset_1(A_15,'#skF_4',B_80) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_225])).

tff(c_918,plain,(
    ! [A_132,B_133,D_134] :
      ( k9_subset_1(u1_struct_0(A_132),B_133,D_134) != '#skF_2'(A_132,B_133)
      | ~ v3_pre_topc(D_134,A_132)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(A_132)))
      | v2_tex_2(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_924,plain,(
    ! [A_132,B_80] :
      ( '#skF_2'(A_132,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_80,A_132)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_132)))
      | v2_tex_2('#skF_4',A_132)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_918])).

tff(c_943,plain,(
    ! [A_135,B_136] :
      ( '#skF_2'(A_135,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | v2_tex_2('#skF_4',A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_924])).

tff(c_952,plain,(
    ! [B_136] :
      ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
      | ~ v3_pre_topc(B_136,'#skF_3')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_943])).

tff(c_964,plain,(
    ! [B_136] :
      ( ~ v3_pre_topc(B_136,'#skF_3')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_367,c_952])).

tff(c_968,plain,(
    ! [B_137] :
      ( ~ v3_pre_topc(B_137,'#skF_3')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_964])).

tff(c_985,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_968])).

tff(c_989,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_985])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.45  
% 2.90/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.45  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.16/1.45  
% 3.16/1.45  %Foreground sorts:
% 3.16/1.45  
% 3.16/1.45  
% 3.16/1.45  %Background operators:
% 3.16/1.45  
% 3.16/1.45  
% 3.16/1.45  %Foreground operators:
% 3.16/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.16/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.16/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.16/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.16/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.16/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.16/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.16/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.16/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.16/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.16/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.45  
% 3.20/1.46  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.20/1.46  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.20/1.46  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.20/1.46  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.20/1.46  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.20/1.46  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.20/1.46  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 3.20/1.46  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.20/1.46  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.46  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.46  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.20/1.46  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.20/1.46  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.20/1.46  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.20/1.46  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.20/1.46  tff(c_28, plain, (![A_21]: (v3_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.20/1.46  tff(c_14, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.46  tff(c_16, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.46  tff(c_53, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.20/1.46  tff(c_42, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.20/1.46  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.20/1.46  tff(c_64, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.46  tff(c_68, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_64])).
% 3.20/1.46  tff(c_20, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.46  tff(c_92, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 3.20/1.46  tff(c_342, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), B_89) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.46  tff(c_356, plain, (![A_90]: (r1_tarski('#skF_2'(A_90, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_92, c_342])).
% 3.20/1.46  tff(c_8, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.20/1.46  tff(c_102, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_8])).
% 3.20/1.46  tff(c_361, plain, (![A_91]: ('#skF_2'(A_91, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_356, c_102])).
% 3.20/1.46  tff(c_364, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_361, c_42])).
% 3.20/1.46  tff(c_367, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_364])).
% 3.20/1.46  tff(c_26, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.46  tff(c_104, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.46  tff(c_109, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_26, c_104])).
% 3.20/1.46  tff(c_113, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_109])).
% 3.20/1.46  tff(c_4, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.46  tff(c_84, plain, (![A_2]: (k3_xboole_0(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_4])).
% 3.20/1.46  tff(c_186, plain, (![A_69, B_70, C_71]: (k9_subset_1(A_69, B_70, C_71)=k3_xboole_0(B_70, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.46  tff(c_190, plain, (![A_15, B_70]: (k9_subset_1(A_15, B_70, '#skF_4')=k3_xboole_0(B_70, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_186])).
% 3.20/1.46  tff(c_193, plain, (![A_15, B_70]: (k9_subset_1(A_15, B_70, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_190])).
% 3.20/1.46  tff(c_221, plain, (![A_78, C_79, B_80]: (k9_subset_1(A_78, C_79, B_80)=k9_subset_1(A_78, B_80, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.46  tff(c_225, plain, (![A_15, B_80]: (k9_subset_1(A_15, B_80, '#skF_4')=k9_subset_1(A_15, '#skF_4', B_80))), inference(resolution, [status(thm)], [c_92, c_221])).
% 3.20/1.46  tff(c_229, plain, (![A_15, B_80]: (k9_subset_1(A_15, '#skF_4', B_80)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_225])).
% 3.20/1.46  tff(c_918, plain, (![A_132, B_133, D_134]: (k9_subset_1(u1_struct_0(A_132), B_133, D_134)!='#skF_2'(A_132, B_133) | ~v3_pre_topc(D_134, A_132) | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0(A_132))) | v2_tex_2(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.46  tff(c_924, plain, (![A_132, B_80]: ('#skF_2'(A_132, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_80, A_132) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_132))) | v2_tex_2('#skF_4', A_132) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(superposition, [status(thm), theory('equality')], [c_229, c_918])).
% 3.20/1.46  tff(c_943, plain, (![A_135, B_136]: ('#skF_2'(A_135, '#skF_4')!='#skF_4' | ~v3_pre_topc(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | v2_tex_2('#skF_4', A_135) | ~l1_pre_topc(A_135))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_924])).
% 3.20/1.46  tff(c_952, plain, (![B_136]: ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v3_pre_topc(B_136, '#skF_3') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_943])).
% 3.20/1.46  tff(c_964, plain, (![B_136]: (~v3_pre_topc(B_136, '#skF_3') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_367, c_952])).
% 3.20/1.46  tff(c_968, plain, (![B_137]: (~v3_pre_topc(B_137, '#skF_3') | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_964])).
% 3.20/1.46  tff(c_985, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_53, c_968])).
% 3.20/1.46  tff(c_989, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_985])).
% 3.20/1.46  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_989])).
% 3.20/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.46  
% 3.20/1.46  Inference rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Ref     : 0
% 3.20/1.46  #Sup     : 218
% 3.20/1.46  #Fact    : 0
% 3.20/1.46  #Define  : 0
% 3.20/1.46  #Split   : 2
% 3.20/1.46  #Chain   : 0
% 3.20/1.46  #Close   : 0
% 3.20/1.46  
% 3.20/1.46  Ordering : KBO
% 3.20/1.46  
% 3.20/1.46  Simplification rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Subsume      : 6
% 3.20/1.46  #Demod        : 237
% 3.20/1.46  #Tautology    : 119
% 3.20/1.46  #SimpNegUnit  : 8
% 3.20/1.46  #BackRed      : 1
% 3.20/1.46  
% 3.20/1.46  #Partial instantiations: 0
% 3.20/1.46  #Strategies tried      : 1
% 3.20/1.46  
% 3.20/1.46  Timing (in seconds)
% 3.20/1.46  ----------------------
% 3.20/1.47  Preprocessing        : 0.31
% 3.20/1.47  Parsing              : 0.17
% 3.20/1.47  CNF conversion       : 0.02
% 3.20/1.47  Main loop            : 0.38
% 3.20/1.47  Inferencing          : 0.14
% 3.20/1.47  Reduction            : 0.13
% 3.20/1.47  Demodulation         : 0.10
% 3.20/1.47  BG Simplification    : 0.02
% 3.20/1.47  Subsumption          : 0.06
% 3.20/1.47  Abstraction          : 0.03
% 3.20/1.47  MUC search           : 0.00
% 3.20/1.47  Cooper               : 0.00
% 3.20/1.47  Total                : 0.73
% 3.20/1.47  Index Insertion      : 0.00
% 3.20/1.47  Index Deletion       : 0.00
% 3.20/1.47  Index Matching       : 0.00
% 3.20/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
