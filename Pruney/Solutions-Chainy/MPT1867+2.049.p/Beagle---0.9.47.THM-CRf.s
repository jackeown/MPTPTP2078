%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:28 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 140 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 284 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_4] : k3_xboole_0(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_12])).

tff(c_16,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_7] : k4_xboole_0(A_7,'#skF_4') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_119,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_119])).

tff(c_151,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_137])).

tff(c_14,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_163,plain,(
    ! [A_61] : r1_tarski('#skF_4',A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_14])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_83,plain,(
    ! [A_13] : m1_subset_1('#skF_4',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_22])).

tff(c_488,plain,(
    ! [A_90,B_91] :
      ( r1_tarski('#skF_2'(A_90,B_91),B_91)
      | v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_493,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_2'(A_92,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_83,c_488])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_498,plain,(
    ! [A_92] :
      ( '#skF_2'(A_92,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_2'(A_92,'#skF_4'))
      | v2_tex_2('#skF_4',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_493,c_6])).

tff(c_503,plain,(
    ! [A_93] :
      ( '#skF_2'(A_93,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_498])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_506,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_503,c_40])).

tff(c_509,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_506])).

tff(c_410,plain,(
    ! [B_85,A_86] :
      ( v4_pre_topc(B_85,A_86)
      | ~ v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_414,plain,(
    ! [A_86] :
      ( v4_pre_topc('#skF_4',A_86)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_83,c_410])).

tff(c_417,plain,(
    ! [A_86] :
      ( v4_pre_topc('#skF_4',A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_414])).

tff(c_310,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_312,plain,(
    ! [A_13,B_75] : k9_subset_1(A_13,B_75,'#skF_4') = k3_xboole_0(B_75,'#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_310])).

tff(c_314,plain,(
    ! [A_13,B_75] : k9_subset_1(A_13,B_75,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_312])).

tff(c_789,plain,(
    ! [A_108,B_109,D_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,D_110) != '#skF_2'(A_108,B_109)
      | ~ v4_pre_topc(D_110,A_108)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_792,plain,(
    ! [A_108,B_75] :
      ( '#skF_2'(A_108,B_75) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_108)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_75,A_108)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_789])).

tff(c_795,plain,(
    ! [A_111,B_112] :
      ( '#skF_2'(A_111,B_112) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_111)
      | v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_792])).

tff(c_805,plain,(
    ! [A_113] :
      ( '#skF_2'(A_113,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_113)
      | v2_tex_2('#skF_4',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_83,c_795])).

tff(c_810,plain,(
    ! [A_114] :
      ( '#skF_2'(A_114,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_417,c_805])).

tff(c_813,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_810,c_40])).

tff(c_817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_509,c_813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.45  
% 2.69/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.45  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.69/1.45  
% 2.69/1.45  %Foreground sorts:
% 2.69/1.45  
% 2.69/1.45  
% 2.69/1.45  %Background operators:
% 2.69/1.45  
% 2.69/1.45  
% 2.69/1.45  %Foreground operators:
% 2.69/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.69/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.69/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.69/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.69/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.69/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.69/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.45  
% 3.00/1.47  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.00/1.47  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.00/1.47  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.00/1.47  tff(f_42, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.00/1.47  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.00/1.47  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.00/1.47  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.00/1.47  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.00/1.47  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.47  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.00/1.47  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.00/1.47  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.47  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.47  tff(c_44, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.47  tff(c_70, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.00/1.47  tff(c_79, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_70])).
% 3.00/1.47  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.47  tff(c_82, plain, (![A_4]: (k3_xboole_0(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_12])).
% 3.00/1.47  tff(c_16, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.00/1.47  tff(c_81, plain, (![A_7]: (k4_xboole_0(A_7, '#skF_4')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_16])).
% 3.00/1.47  tff(c_119, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.47  tff(c_137, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_119])).
% 3.00/1.47  tff(c_151, plain, (![A_61]: (k4_xboole_0(A_61, A_61)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_137])).
% 3.00/1.47  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.47  tff(c_163, plain, (![A_61]: (r1_tarski('#skF_4', A_61))), inference(superposition, [status(thm), theory('equality')], [c_151, c_14])).
% 3.00/1.47  tff(c_22, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.00/1.47  tff(c_83, plain, (![A_13]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_22])).
% 3.00/1.47  tff(c_488, plain, (![A_90, B_91]: (r1_tarski('#skF_2'(A_90, B_91), B_91) | v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.00/1.47  tff(c_493, plain, (![A_92]: (r1_tarski('#skF_2'(A_92, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_83, c_488])).
% 3.00/1.47  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.00/1.47  tff(c_498, plain, (![A_92]: ('#skF_2'(A_92, '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_2'(A_92, '#skF_4')) | v2_tex_2('#skF_4', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_493, c_6])).
% 3.00/1.47  tff(c_503, plain, (![A_93]: ('#skF_2'(A_93, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_93) | ~l1_pre_topc(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_498])).
% 3.00/1.47  tff(c_40, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.00/1.47  tff(c_506, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_503, c_40])).
% 3.00/1.47  tff(c_509, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_506])).
% 3.00/1.47  tff(c_410, plain, (![B_85, A_86]: (v4_pre_topc(B_85, A_86) | ~v1_xboole_0(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.47  tff(c_414, plain, (![A_86]: (v4_pre_topc('#skF_4', A_86) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(resolution, [status(thm)], [c_83, c_410])).
% 3.00/1.47  tff(c_417, plain, (![A_86]: (v4_pre_topc('#skF_4', A_86) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_414])).
% 3.00/1.47  tff(c_310, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.47  tff(c_312, plain, (![A_13, B_75]: (k9_subset_1(A_13, B_75, '#skF_4')=k3_xboole_0(B_75, '#skF_4'))), inference(resolution, [status(thm)], [c_83, c_310])).
% 3.00/1.47  tff(c_314, plain, (![A_13, B_75]: (k9_subset_1(A_13, B_75, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_312])).
% 3.00/1.47  tff(c_789, plain, (![A_108, B_109, D_110]: (k9_subset_1(u1_struct_0(A_108), B_109, D_110)!='#skF_2'(A_108, B_109) | ~v4_pre_topc(D_110, A_108) | ~m1_subset_1(D_110, k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.00/1.47  tff(c_792, plain, (![A_108, B_75]: ('#skF_2'(A_108, B_75)!='#skF_4' | ~v4_pre_topc('#skF_4', A_108) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_75, A_108) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(superposition, [status(thm), theory('equality')], [c_314, c_789])).
% 3.00/1.47  tff(c_795, plain, (![A_111, B_112]: ('#skF_2'(A_111, B_112)!='#skF_4' | ~v4_pre_topc('#skF_4', A_111) | v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_792])).
% 3.00/1.47  tff(c_805, plain, (![A_113]: ('#skF_2'(A_113, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_113) | v2_tex_2('#skF_4', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_83, c_795])).
% 3.00/1.47  tff(c_810, plain, (![A_114]: ('#skF_2'(A_114, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(resolution, [status(thm)], [c_417, c_805])).
% 3.00/1.47  tff(c_813, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_810, c_40])).
% 3.00/1.47  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_509, c_813])).
% 3.00/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.47  
% 3.00/1.47  Inference rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Ref     : 0
% 3.00/1.47  #Sup     : 174
% 3.00/1.47  #Fact    : 0
% 3.00/1.47  #Define  : 0
% 3.00/1.47  #Split   : 0
% 3.00/1.47  #Chain   : 0
% 3.00/1.47  #Close   : 0
% 3.00/1.47  
% 3.00/1.47  Ordering : KBO
% 3.00/1.47  
% 3.00/1.47  Simplification rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Subsume      : 9
% 3.00/1.47  #Demod        : 203
% 3.00/1.47  #Tautology    : 123
% 3.00/1.47  #SimpNegUnit  : 2
% 3.00/1.47  #BackRed      : 5
% 3.00/1.47  
% 3.00/1.47  #Partial instantiations: 0
% 3.00/1.47  #Strategies tried      : 1
% 3.00/1.47  
% 3.00/1.47  Timing (in seconds)
% 3.00/1.47  ----------------------
% 3.00/1.47  Preprocessing        : 0.33
% 3.00/1.47  Parsing              : 0.18
% 3.00/1.47  CNF conversion       : 0.02
% 3.00/1.47  Main loop            : 0.31
% 3.00/1.47  Inferencing          : 0.12
% 3.00/1.47  Reduction            : 0.12
% 3.00/1.47  Demodulation         : 0.09
% 3.00/1.47  BG Simplification    : 0.02
% 3.00/1.47  Subsumption          : 0.04
% 3.00/1.47  Abstraction          : 0.02
% 3.00/1.47  MUC search           : 0.00
% 3.00/1.47  Cooper               : 0.00
% 3.00/1.47  Total                : 0.68
% 3.00/1.47  Index Insertion      : 0.00
% 3.00/1.47  Index Deletion       : 0.00
% 3.00/1.47  Index Matching       : 0.00
% 3.00/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
