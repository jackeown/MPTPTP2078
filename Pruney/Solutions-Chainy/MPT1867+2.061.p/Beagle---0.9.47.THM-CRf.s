%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:30 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 122 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 255 expanded)
%              Number of equality atoms :   23 (  48 expanded)
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

tff(f_97,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
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
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_53,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_14])).

tff(c_187,plain,(
    ! [A_68,B_69] :
      ( r1_tarski('#skF_2'(A_68,B_69),B_69)
      | v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_192,plain,(
    ! [A_70] :
      ( r1_tarski('#skF_2'(A_70,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_55,c_187])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_53,c_8])).

tff(c_197,plain,(
    ! [A_71] :
      ( '#skF_2'(A_71,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_192,c_78])).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_200,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_32])).

tff(c_203,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_200])).

tff(c_178,plain,(
    ! [B_65,A_66] :
      ( v4_pre_topc(B_65,A_66)
      | ~ v1_xboole_0(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_182,plain,(
    ! [A_66] :
      ( v4_pre_topc('#skF_4',A_66)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_55,c_178])).

tff(c_185,plain,(
    ! [A_66] :
      ( v4_pre_topc('#skF_4',A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_182])).

tff(c_6,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_2] : k3_xboole_0(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_53,c_6])).

tff(c_128,plain,(
    ! [A_58,B_59,C_60] :
      ( k9_subset_1(A_58,B_59,C_60) = k3_xboole_0(B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [A_9,B_59] : k9_subset_1(A_9,B_59,'#skF_4') = k3_xboole_0(B_59,'#skF_4') ),
    inference(resolution,[status(thm)],[c_55,c_128])).

tff(c_132,plain,(
    ! [A_9,B_59] : k9_subset_1(A_9,B_59,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_130])).

tff(c_382,plain,(
    ! [A_83,B_84,D_85] :
      ( k9_subset_1(u1_struct_0(A_83),B_84,D_85) != '#skF_2'(A_83,B_84)
      | ~ v4_pre_topc(D_85,A_83)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(u1_struct_0(A_83)))
      | v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_385,plain,(
    ! [A_83,B_59] :
      ( '#skF_2'(A_83,B_59) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_83)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_83)))
      | v2_tex_2(B_59,A_83)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_382])).

tff(c_388,plain,(
    ! [A_86,B_87] :
      ( '#skF_2'(A_86,B_87) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_86)
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_385])).

tff(c_398,plain,(
    ! [A_88] :
      ( '#skF_2'(A_88,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_88)
      | v2_tex_2('#skF_4',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_55,c_388])).

tff(c_403,plain,(
    ! [A_89] :
      ( '#skF_2'(A_89,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_185,c_398])).

tff(c_406,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_403,c_32])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_203,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:58:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.28  
% 2.23/1.28  %Foreground sorts:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Background operators:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Foreground operators:
% 2.23/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.23/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.23/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.28  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.23/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.28  
% 2.23/1.29  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.23/1.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.29  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.23/1.29  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.23/1.29  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.23/1.29  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.23/1.29  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.23/1.29  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.23/1.29  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.29  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.29  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.29  tff(c_44, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.23/1.29  tff(c_53, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.23/1.29  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.29  tff(c_55, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_14])).
% 2.23/1.29  tff(c_187, plain, (![A_68, B_69]: (r1_tarski('#skF_2'(A_68, B_69), B_69) | v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.29  tff(c_192, plain, (![A_70]: (r1_tarski('#skF_2'(A_70, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_55, c_187])).
% 2.23/1.29  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.29  tff(c_78, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_53, c_8])).
% 2.23/1.29  tff(c_197, plain, (![A_71]: ('#skF_2'(A_71, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_192, c_78])).
% 2.23/1.29  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.29  tff(c_200, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_197, c_32])).
% 2.23/1.29  tff(c_203, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_200])).
% 2.23/1.29  tff(c_178, plain, (![B_65, A_66]: (v4_pre_topc(B_65, A_66) | ~v1_xboole_0(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.29  tff(c_182, plain, (![A_66]: (v4_pre_topc('#skF_4', A_66) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(resolution, [status(thm)], [c_55, c_178])).
% 2.23/1.29  tff(c_185, plain, (![A_66]: (v4_pre_topc('#skF_4', A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_182])).
% 2.23/1.29  tff(c_6, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.29  tff(c_62, plain, (![A_2]: (k3_xboole_0(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_53, c_6])).
% 2.23/1.29  tff(c_128, plain, (![A_58, B_59, C_60]: (k9_subset_1(A_58, B_59, C_60)=k3_xboole_0(B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.29  tff(c_130, plain, (![A_9, B_59]: (k9_subset_1(A_9, B_59, '#skF_4')=k3_xboole_0(B_59, '#skF_4'))), inference(resolution, [status(thm)], [c_55, c_128])).
% 2.23/1.29  tff(c_132, plain, (![A_9, B_59]: (k9_subset_1(A_9, B_59, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_130])).
% 2.23/1.29  tff(c_382, plain, (![A_83, B_84, D_85]: (k9_subset_1(u1_struct_0(A_83), B_84, D_85)!='#skF_2'(A_83, B_84) | ~v4_pre_topc(D_85, A_83) | ~m1_subset_1(D_85, k1_zfmisc_1(u1_struct_0(A_83))) | v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.29  tff(c_385, plain, (![A_83, B_59]: ('#skF_2'(A_83, B_59)!='#skF_4' | ~v4_pre_topc('#skF_4', A_83) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_83))) | v2_tex_2(B_59, A_83) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(superposition, [status(thm), theory('equality')], [c_132, c_382])).
% 2.23/1.29  tff(c_388, plain, (![A_86, B_87]: ('#skF_2'(A_86, B_87)!='#skF_4' | ~v4_pre_topc('#skF_4', A_86) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_385])).
% 2.23/1.29  tff(c_398, plain, (![A_88]: ('#skF_2'(A_88, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_88) | v2_tex_2('#skF_4', A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_55, c_388])).
% 2.23/1.29  tff(c_403, plain, (![A_89]: ('#skF_2'(A_89, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(resolution, [status(thm)], [c_185, c_398])).
% 2.23/1.29  tff(c_406, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_403, c_32])).
% 2.23/1.29  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_203, c_406])).
% 2.23/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  Inference rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Ref     : 0
% 2.23/1.29  #Sup     : 86
% 2.23/1.29  #Fact    : 0
% 2.23/1.29  #Define  : 0
% 2.23/1.29  #Split   : 0
% 2.23/1.29  #Chain   : 0
% 2.23/1.29  #Close   : 0
% 2.23/1.29  
% 2.23/1.29  Ordering : KBO
% 2.23/1.29  
% 2.23/1.29  Simplification rules
% 2.23/1.29  ----------------------
% 2.23/1.29  #Subsume      : 0
% 2.23/1.29  #Demod        : 83
% 2.23/1.29  #Tautology    : 52
% 2.23/1.30  #SimpNegUnit  : 2
% 2.23/1.30  #BackRed      : 3
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.30  Preprocessing        : 0.31
% 2.23/1.30  Parsing              : 0.16
% 2.23/1.30  CNF conversion       : 0.02
% 2.23/1.30  Main loop            : 0.24
% 2.23/1.30  Inferencing          : 0.09
% 2.23/1.30  Reduction            : 0.08
% 2.23/1.30  Demodulation         : 0.07
% 2.23/1.30  BG Simplification    : 0.02
% 2.23/1.30  Subsumption          : 0.03
% 2.23/1.30  Abstraction          : 0.02
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.58
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
