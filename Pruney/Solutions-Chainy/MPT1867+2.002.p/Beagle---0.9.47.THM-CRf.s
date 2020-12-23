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
% DateTime   : Thu Dec  3 10:29:22 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 174 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  120 ( 357 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_10,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_166,plain,(
    ! [A_73,B_74] :
      ( r1_tarski('#skF_2'(A_73,B_74),B_74)
      | v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_177,plain,(
    ! [A_76] :
      ( r1_tarski('#skF_2'(A_76,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_48,c_166])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ r1_tarski(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_4])).

tff(c_200,plain,(
    ! [A_79] :
      ( '#skF_2'(A_79,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_177,c_61])).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_203,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_30])).

tff(c_206,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203])).

tff(c_114,plain,(
    ! [B_67,A_68] :
      ( v3_pre_topc(B_67,A_68)
      | ~ v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_126,plain,(
    ! [A_68] :
      ( v3_pre_topc('#skF_4',A_68)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_131,plain,(
    ! [A_68] :
      ( v3_pre_topc('#skF_4',A_68)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_126])).

tff(c_74,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_9,B_58] : k9_subset_1(A_9,B_58,'#skF_4') = k3_xboole_0(B_58,'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_87,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1(k9_subset_1(A_62,B_63,C_64),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [B_58,A_9] :
      ( m1_subset_1(k3_xboole_0(B_58,'#skF_4'),k1_zfmisc_1(A_9))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_87])).

tff(c_103,plain,(
    ! [B_65,A_66] : m1_subset_1(k3_xboole_0(B_65,'#skF_4'),k1_zfmisc_1(A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_97])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [B_65,A_66] :
      ( v1_xboole_0(k3_xboole_0(B_65,'#skF_4'))
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_103,c_12])).

tff(c_132,plain,(
    ! [A_66] : ~ v1_xboole_0(A_66) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_34])).

tff(c_137,plain,(
    ! [B_69] : v1_xboole_0(k3_xboole_0(B_69,'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_141,plain,(
    ! [B_69] : k3_xboole_0(B_69,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_137,c_47])).

tff(c_144,plain,(
    ! [A_9,B_58] : k9_subset_1(A_9,B_58,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_77])).

tff(c_387,plain,(
    ! [A_113,B_114,D_115] :
      ( k9_subset_1(u1_struct_0(A_113),B_114,D_115) != '#skF_2'(A_113,B_114)
      | ~ v3_pre_topc(D_115,A_113)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_393,plain,(
    ! [A_113,B_58] :
      ( '#skF_2'(A_113,B_58) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_113)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tex_2(B_58,A_113)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_387])).

tff(c_396,plain,(
    ! [A_116,B_117] :
      ( '#skF_2'(A_116,B_117) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_116)
      | v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_393])).

tff(c_415,plain,(
    ! [A_118] :
      ( '#skF_2'(A_118,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_118)
      | v2_tex_2('#skF_4',A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_48,c_396])).

tff(c_420,plain,(
    ! [A_119] :
      ( '#skF_2'(A_119,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_131,c_415])).

tff(c_423,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_420,c_30])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_206,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.85  
% 3.17/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.86  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.33/1.86  
% 3.33/1.86  %Foreground sorts:
% 3.33/1.86  
% 3.33/1.86  
% 3.33/1.86  %Background operators:
% 3.33/1.86  
% 3.33/1.86  
% 3.33/1.86  %Foreground operators:
% 3.33/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.33/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.86  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.33/1.86  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.86  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.33/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.33/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.86  
% 3.33/1.88  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.33/1.88  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.33/1.88  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.33/1.88  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.33/1.88  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.33/1.88  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.33/1.88  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.33/1.88  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.33/1.88  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.33/1.88  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.88  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.88  tff(c_34, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.88  tff(c_42, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.88  tff(c_46, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_42])).
% 3.33/1.88  tff(c_10, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.88  tff(c_48, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 3.33/1.88  tff(c_166, plain, (![A_73, B_74]: (r1_tarski('#skF_2'(A_73, B_74), B_74) | v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.88  tff(c_177, plain, (![A_76]: (r1_tarski('#skF_2'(A_76, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_48, c_166])).
% 3.33/1.88  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.88  tff(c_61, plain, (![A_2]: (A_2='#skF_4' | ~r1_tarski(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_4])).
% 3.33/1.88  tff(c_200, plain, (![A_79]: ('#skF_2'(A_79, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_177, c_61])).
% 3.33/1.88  tff(c_30, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.33/1.88  tff(c_203, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_200, c_30])).
% 3.33/1.88  tff(c_206, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_203])).
% 3.33/1.88  tff(c_114, plain, (![B_67, A_68]: (v3_pre_topc(B_67, A_68) | ~v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.33/1.88  tff(c_126, plain, (![A_68]: (v3_pre_topc('#skF_4', A_68) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(resolution, [status(thm)], [c_48, c_114])).
% 3.33/1.88  tff(c_131, plain, (![A_68]: (v3_pre_topc('#skF_4', A_68) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_126])).
% 3.33/1.88  tff(c_74, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.88  tff(c_77, plain, (![A_9, B_58]: (k9_subset_1(A_9, B_58, '#skF_4')=k3_xboole_0(B_58, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_74])).
% 3.33/1.88  tff(c_87, plain, (![A_62, B_63, C_64]: (m1_subset_1(k9_subset_1(A_62, B_63, C_64), k1_zfmisc_1(A_62)) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.88  tff(c_97, plain, (![B_58, A_9]: (m1_subset_1(k3_xboole_0(B_58, '#skF_4'), k1_zfmisc_1(A_9)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_87])).
% 3.33/1.88  tff(c_103, plain, (![B_65, A_66]: (m1_subset_1(k3_xboole_0(B_65, '#skF_4'), k1_zfmisc_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_97])).
% 3.33/1.88  tff(c_12, plain, (![B_12, A_10]: (v1_xboole_0(B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.88  tff(c_113, plain, (![B_65, A_66]: (v1_xboole_0(k3_xboole_0(B_65, '#skF_4')) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_103, c_12])).
% 3.33/1.88  tff(c_132, plain, (![A_66]: (~v1_xboole_0(A_66))), inference(splitLeft, [status(thm)], [c_113])).
% 3.33/1.88  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_34])).
% 3.33/1.88  tff(c_137, plain, (![B_69]: (v1_xboole_0(k3_xboole_0(B_69, '#skF_4')))), inference(splitRight, [status(thm)], [c_113])).
% 3.33/1.88  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.88  tff(c_47, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2])).
% 3.33/1.88  tff(c_141, plain, (![B_69]: (k3_xboole_0(B_69, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_137, c_47])).
% 3.33/1.88  tff(c_144, plain, (![A_9, B_58]: (k9_subset_1(A_9, B_58, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_77])).
% 3.33/1.88  tff(c_387, plain, (![A_113, B_114, D_115]: (k9_subset_1(u1_struct_0(A_113), B_114, D_115)!='#skF_2'(A_113, B_114) | ~v3_pre_topc(D_115, A_113) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_113))) | v2_tex_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.33/1.88  tff(c_393, plain, (![A_113, B_58]: ('#skF_2'(A_113, B_58)!='#skF_4' | ~v3_pre_topc('#skF_4', A_113) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_113))) | v2_tex_2(B_58, A_113) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(superposition, [status(thm), theory('equality')], [c_144, c_387])).
% 3.33/1.88  tff(c_396, plain, (![A_116, B_117]: ('#skF_2'(A_116, B_117)!='#skF_4' | ~v3_pre_topc('#skF_4', A_116) | v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_393])).
% 3.33/1.88  tff(c_415, plain, (![A_118]: ('#skF_2'(A_118, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_118) | v2_tex_2('#skF_4', A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_48, c_396])).
% 3.33/1.88  tff(c_420, plain, (![A_119]: ('#skF_2'(A_119, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(resolution, [status(thm)], [c_131, c_415])).
% 3.33/1.88  tff(c_423, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_420, c_30])).
% 3.33/1.88  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_206, c_423])).
% 3.33/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.88  
% 3.33/1.88  Inference rules
% 3.33/1.88  ----------------------
% 3.33/1.88  #Ref     : 0
% 3.33/1.88  #Sup     : 86
% 3.33/1.88  #Fact    : 0
% 3.33/1.88  #Define  : 0
% 3.33/1.88  #Split   : 1
% 3.33/1.88  #Chain   : 0
% 3.33/1.88  #Close   : 0
% 3.33/1.88  
% 3.33/1.88  Ordering : KBO
% 3.33/1.88  
% 3.33/1.88  Simplification rules
% 3.33/1.88  ----------------------
% 3.33/1.88  #Subsume      : 8
% 3.33/1.88  #Demod        : 57
% 3.33/1.88  #Tautology    : 33
% 3.33/1.88  #SimpNegUnit  : 4
% 3.33/1.88  #BackRed      : 6
% 3.33/1.88  
% 3.33/1.88  #Partial instantiations: 0
% 3.33/1.88  #Strategies tried      : 1
% 3.33/1.88  
% 3.33/1.88  Timing (in seconds)
% 3.33/1.88  ----------------------
% 3.33/1.89  Preprocessing        : 0.52
% 3.33/1.89  Parsing              : 0.27
% 3.33/1.89  CNF conversion       : 0.04
% 3.33/1.89  Main loop            : 0.46
% 3.33/1.89  Inferencing          : 0.17
% 3.33/1.89  Reduction            : 0.13
% 3.33/1.89  Demodulation         : 0.09
% 3.33/1.89  BG Simplification    : 0.03
% 3.33/1.89  Subsumption          : 0.09
% 3.33/1.89  Abstraction          : 0.03
% 3.33/1.89  MUC search           : 0.00
% 3.33/1.89  Cooper               : 0.00
% 3.33/1.89  Total                : 1.04
% 3.33/1.89  Index Insertion      : 0.00
% 3.33/1.89  Index Deletion       : 0.00
% 3.33/1.89  Index Matching       : 0.00
% 3.33/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
