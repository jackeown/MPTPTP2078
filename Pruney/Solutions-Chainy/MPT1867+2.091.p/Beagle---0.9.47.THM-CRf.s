%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 148 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 296 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

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

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

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
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_6,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_140,plain,(
    ! [A_69,B_70] :
      ( r1_tarski('#skF_2'(A_69,B_70),B_70)
      | v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_145,plain,(
    ! [A_71] :
      ( r1_tarski('#skF_2'(A_71,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_50,c_140])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k2_xboole_0(A_2,B_3) = B_3
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [A_71] :
      ( k2_xboole_0('#skF_2'(A_71,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_151,plain,(
    ! [A_72] :
      ( '#skF_2'(A_72,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_148])).

tff(c_154,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_151,c_32])).

tff(c_157,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_154])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tops_1(A_62,B_63),B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    ! [A_66] :
      ( r1_tarski(k1_tops_1(A_66,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_112,plain,(
    ! [A_66] :
      ( k2_xboole_0(k1_tops_1(A_66,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_115,plain,(
    ! [A_67] :
      ( k1_tops_1(A_67,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_112])).

tff(c_119,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_104,plain,(
    ! [A_64,B_65] :
      ( v3_pre_topc(k1_tops_1(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,(
    ! [A_68] :
      ( v3_pre_topc(k1_tops_1(A_68,'#skF_4'),A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_137,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_134])).

tff(c_139,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_137])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_8])).

tff(c_86,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(A_55,B_56,C_57) = k3_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_9,B_56] : k9_subset_1(A_9,B_56,'#skF_4') = k3_xboole_0(B_56,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_90,plain,(
    ! [A_9,B_56] : k9_subset_1(A_9,B_56,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_88])).

tff(c_325,plain,(
    ! [A_100,B_101,D_102] :
      ( k9_subset_1(u1_struct_0(A_100),B_101,D_102) != '#skF_2'(A_100,B_101)
      | ~ v3_pre_topc(D_102,A_100)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0(A_100)))
      | v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_330,plain,(
    ! [A_100,B_56] :
      ( '#skF_2'(A_100,B_56) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_100)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_100)))
      | v2_tex_2(B_56,A_100)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_325])).

tff(c_333,plain,(
    ! [A_103,B_104] :
      ( '#skF_2'(A_103,B_104) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_103)
      | v2_tex_2(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_330])).

tff(c_347,plain,(
    ! [A_105] :
      ( '#skF_2'(A_105,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_105)
      | v2_tex_2('#skF_4',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_50,c_333])).

tff(c_350,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_347])).

tff(c_353,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_157,c_350])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.35  
% 2.40/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.35  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.40/1.35  
% 2.40/1.35  %Foreground sorts:
% 2.40/1.35  
% 2.40/1.35  
% 2.40/1.35  %Background operators:
% 2.40/1.35  
% 2.40/1.35  
% 2.40/1.35  %Foreground operators:
% 2.40/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.40/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.35  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.40/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.40/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.40/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.35  
% 2.66/1.37  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.66/1.37  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.66/1.37  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.66/1.37  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.66/1.37  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.66/1.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.66/1.37  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.66/1.37  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.66/1.37  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.66/1.37  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.66/1.37  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.37  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.37  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.37  tff(c_44, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.37  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.66/1.37  tff(c_6, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.37  tff(c_55, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 2.66/1.37  tff(c_12, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.37  tff(c_50, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 2.66/1.37  tff(c_140, plain, (![A_69, B_70]: (r1_tarski('#skF_2'(A_69, B_70), B_70) | v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.37  tff(c_145, plain, (![A_71]: (r1_tarski('#skF_2'(A_71, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_50, c_140])).
% 2.66/1.37  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, B_3)=B_3 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.37  tff(c_148, plain, (![A_71]: (k2_xboole_0('#skF_2'(A_71, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_145, c_4])).
% 2.66/1.37  tff(c_151, plain, (![A_72]: ('#skF_2'(A_72, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_148])).
% 2.66/1.37  tff(c_154, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_151, c_32])).
% 2.66/1.37  tff(c_157, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_154])).
% 2.66/1.37  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.66/1.37  tff(c_99, plain, (![A_62, B_63]: (r1_tarski(k1_tops_1(A_62, B_63), B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.66/1.37  tff(c_109, plain, (![A_66]: (r1_tarski(k1_tops_1(A_66, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_50, c_99])).
% 2.66/1.37  tff(c_112, plain, (![A_66]: (k2_xboole_0(k1_tops_1(A_66, '#skF_4'), '#skF_4')='#skF_4' | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_109, c_4])).
% 2.66/1.37  tff(c_115, plain, (![A_67]: (k1_tops_1(A_67, '#skF_4')='#skF_4' | ~l1_pre_topc(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_112])).
% 2.66/1.37  tff(c_119, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_115])).
% 2.66/1.37  tff(c_104, plain, (![A_64, B_65]: (v3_pre_topc(k1_tops_1(A_64, B_65), A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.37  tff(c_134, plain, (![A_68]: (v3_pre_topc(k1_tops_1(A_68, '#skF_4'), A_68) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(resolution, [status(thm)], [c_50, c_104])).
% 2.66/1.37  tff(c_137, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_119, c_134])).
% 2.66/1.37  tff(c_139, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_137])).
% 2.66/1.37  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.37  tff(c_65, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_8])).
% 2.66/1.37  tff(c_86, plain, (![A_55, B_56, C_57]: (k9_subset_1(A_55, B_56, C_57)=k3_xboole_0(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.37  tff(c_88, plain, (![A_9, B_56]: (k9_subset_1(A_9, B_56, '#skF_4')=k3_xboole_0(B_56, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 2.66/1.37  tff(c_90, plain, (![A_9, B_56]: (k9_subset_1(A_9, B_56, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_88])).
% 2.66/1.37  tff(c_325, plain, (![A_100, B_101, D_102]: (k9_subset_1(u1_struct_0(A_100), B_101, D_102)!='#skF_2'(A_100, B_101) | ~v3_pre_topc(D_102, A_100) | ~m1_subset_1(D_102, k1_zfmisc_1(u1_struct_0(A_100))) | v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.37  tff(c_330, plain, (![A_100, B_56]: ('#skF_2'(A_100, B_56)!='#skF_4' | ~v3_pre_topc('#skF_4', A_100) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_100))) | v2_tex_2(B_56, A_100) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(superposition, [status(thm), theory('equality')], [c_90, c_325])).
% 2.66/1.37  tff(c_333, plain, (![A_103, B_104]: ('#skF_2'(A_103, B_104)!='#skF_4' | ~v3_pre_topc('#skF_4', A_103) | v2_tex_2(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_330])).
% 2.66/1.37  tff(c_347, plain, (![A_105]: ('#skF_2'(A_105, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_105) | v2_tex_2('#skF_4', A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_50, c_333])).
% 2.66/1.37  tff(c_350, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_139, c_347])).
% 2.66/1.37  tff(c_353, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_157, c_350])).
% 2.66/1.37  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_353])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 68
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 0
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 1
% 2.66/1.37  #Demod        : 68
% 2.66/1.37  #Tautology    : 29
% 2.66/1.37  #SimpNegUnit  : 12
% 2.66/1.37  #BackRed      : 2
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.37  Preprocessing        : 0.33
% 2.66/1.37  Parsing              : 0.17
% 2.66/1.37  CNF conversion       : 0.03
% 2.66/1.37  Main loop            : 0.26
% 2.66/1.37  Inferencing          : 0.10
% 2.66/1.37  Reduction            : 0.08
% 2.66/1.37  Demodulation         : 0.06
% 2.66/1.37  BG Simplification    : 0.02
% 2.66/1.37  Subsumption          : 0.04
% 2.66/1.37  Abstraction          : 0.02
% 2.66/1.37  MUC search           : 0.00
% 2.66/1.37  Cooper               : 0.00
% 2.66/1.37  Total                : 0.63
% 2.66/1.37  Index Insertion      : 0.00
% 2.66/1.37  Index Deletion       : 0.00
% 2.66/1.37  Index Matching       : 0.00
% 2.66/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
