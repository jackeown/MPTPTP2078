%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 177 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 422 expanded)
%              Number of equality atoms :   18 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_77,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_26,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_37,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_8])).

tff(c_86,plain,(
    ! [A_56,B_57] :
      ( r1_tarski('#skF_2'(A_56,B_57),B_57)
      | v2_tex_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_91,plain,(
    ! [A_58] :
      ( r1_tarski('#skF_2'(A_58,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_47,c_86])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ r1_tarski(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_41,c_4])).

tff(c_107,plain,(
    ! [A_61] :
      ( '#skF_2'(A_61,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_91,c_56])).

tff(c_110,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_26])).

tff(c_113,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_96,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1('#skF_2'(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( v3_pre_topc(B_12,A_10)
      | ~ v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_141,plain,(
    ! [A_65,B_66] :
      ( v3_pre_topc('#skF_2'(A_65,B_66),A_65)
      | ~ v1_xboole_0('#skF_2'(A_65,B_66))
      | ~ v2_pre_topc(A_65)
      | v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_96,c_12])).

tff(c_157,plain,(
    ! [A_70] :
      ( v3_pre_topc('#skF_2'(A_70,'#skF_4'),A_70)
      | ~ v1_xboole_0('#skF_2'(A_70,'#skF_4'))
      | ~ v2_pre_topc(A_70)
      | v2_tex_2('#skF_4',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_47,c_141])).

tff(c_160,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_157])).

tff(c_162,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_30,c_113,c_160])).

tff(c_163,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_162])).

tff(c_58,plain,(
    ! [A_43,B_44,C_45] :
      ( k9_subset_1(A_43,B_44,B_44) = B_44
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_6,B_44] : k9_subset_1(A_6,B_44,B_44) = B_44 ),
    inference(resolution,[status(thm)],[c_47,c_58])).

tff(c_208,plain,(
    ! [A_79,B_80,D_81] :
      ( k9_subset_1(u1_struct_0(A_79),B_80,D_81) != '#skF_2'(A_79,B_80)
      | ~ v3_pre_topc(D_81,A_79)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(u1_struct_0(A_79)))
      | v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_212,plain,(
    ! [A_82,B_83] :
      ( '#skF_2'(A_82,B_83) != B_83
      | ~ v3_pre_topc(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | v2_tex_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_208])).

tff(c_219,plain,(
    ! [A_82] :
      ( '#skF_2'(A_82,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_82)
      | v2_tex_2('#skF_4',A_82)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_47,c_212])).

tff(c_225,plain,(
    ! [A_84] :
      ( '#skF_2'(A_84,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_84)
      | v2_tex_2('#skF_4',A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_219])).

tff(c_228,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_163,c_225])).

tff(c_234,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_113,c_228])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:30:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.21/1.24  
% 2.21/1.24  %Foreground sorts:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Background operators:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Foreground operators:
% 2.21/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.21/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.21/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.24  
% 2.21/1.25  tff(f_92, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.21/1.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.21/1.25  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.21/1.25  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.21/1.25  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.21/1.25  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.21/1.25  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.21/1.25  tff(c_26, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.25  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.25  tff(c_30, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.25  tff(c_37, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.25  tff(c_41, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_37])).
% 2.21/1.25  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.25  tff(c_47, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_8])).
% 2.21/1.25  tff(c_86, plain, (![A_56, B_57]: (r1_tarski('#skF_2'(A_56, B_57), B_57) | v2_tex_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.25  tff(c_91, plain, (![A_58]: (r1_tarski('#skF_2'(A_58, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_47, c_86])).
% 2.21/1.25  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.25  tff(c_56, plain, (![A_2]: (A_2='#skF_4' | ~r1_tarski(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_41, c_4])).
% 2.21/1.25  tff(c_107, plain, (![A_61]: ('#skF_2'(A_61, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_91, c_56])).
% 2.21/1.25  tff(c_110, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_107, c_26])).
% 2.21/1.25  tff(c_113, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110])).
% 2.21/1.25  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.21/1.25  tff(c_96, plain, (![A_59, B_60]: (m1_subset_1('#skF_2'(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.25  tff(c_12, plain, (![B_12, A_10]: (v3_pre_topc(B_12, A_10) | ~v1_xboole_0(B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.25  tff(c_141, plain, (![A_65, B_66]: (v3_pre_topc('#skF_2'(A_65, B_66), A_65) | ~v1_xboole_0('#skF_2'(A_65, B_66)) | ~v2_pre_topc(A_65) | v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_96, c_12])).
% 2.21/1.25  tff(c_157, plain, (![A_70]: (v3_pre_topc('#skF_2'(A_70, '#skF_4'), A_70) | ~v1_xboole_0('#skF_2'(A_70, '#skF_4')) | ~v2_pre_topc(A_70) | v2_tex_2('#skF_4', A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_47, c_141])).
% 2.21/1.25  tff(c_160, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_113, c_157])).
% 2.21/1.25  tff(c_162, plain, (v3_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_30, c_113, c_160])).
% 2.21/1.25  tff(c_163, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_162])).
% 2.21/1.25  tff(c_58, plain, (![A_43, B_44, C_45]: (k9_subset_1(A_43, B_44, B_44)=B_44 | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.25  tff(c_61, plain, (![A_6, B_44]: (k9_subset_1(A_6, B_44, B_44)=B_44)), inference(resolution, [status(thm)], [c_47, c_58])).
% 2.21/1.25  tff(c_208, plain, (![A_79, B_80, D_81]: (k9_subset_1(u1_struct_0(A_79), B_80, D_81)!='#skF_2'(A_79, B_80) | ~v3_pre_topc(D_81, A_79) | ~m1_subset_1(D_81, k1_zfmisc_1(u1_struct_0(A_79))) | v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.25  tff(c_212, plain, (![A_82, B_83]: ('#skF_2'(A_82, B_83)!=B_83 | ~v3_pre_topc(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | v2_tex_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_61, c_208])).
% 2.21/1.25  tff(c_219, plain, (![A_82]: ('#skF_2'(A_82, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_82) | v2_tex_2('#skF_4', A_82) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_47, c_212])).
% 2.21/1.26  tff(c_225, plain, (![A_84]: ('#skF_2'(A_84, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_84) | v2_tex_2('#skF_4', A_84) | ~l1_pre_topc(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_219])).
% 2.21/1.26  tff(c_228, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_163, c_225])).
% 2.21/1.26  tff(c_234, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113, c_228])).
% 2.21/1.26  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_234])).
% 2.21/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  Inference rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Ref     : 0
% 2.21/1.26  #Sup     : 42
% 2.21/1.26  #Fact    : 0
% 2.21/1.26  #Define  : 0
% 2.21/1.26  #Split   : 0
% 2.21/1.26  #Chain   : 0
% 2.21/1.26  #Close   : 0
% 2.21/1.26  
% 2.21/1.26  Ordering : KBO
% 2.21/1.26  
% 2.21/1.26  Simplification rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Subsume      : 2
% 2.21/1.26  #Demod        : 34
% 2.21/1.26  #Tautology    : 13
% 2.21/1.26  #SimpNegUnit  : 7
% 2.21/1.26  #BackRed      : 1
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.26  Preprocessing        : 0.29
% 2.21/1.26  Parsing              : 0.16
% 2.21/1.26  CNF conversion       : 0.02
% 2.21/1.26  Main loop            : 0.21
% 2.21/1.26  Inferencing          : 0.09
% 2.21/1.26  Reduction            : 0.06
% 2.21/1.26  Demodulation         : 0.04
% 2.21/1.26  BG Simplification    : 0.01
% 2.21/1.26  Subsumption          : 0.04
% 2.21/1.26  Abstraction          : 0.01
% 2.21/1.26  MUC search           : 0.00
% 2.21/1.26  Cooper               : 0.00
% 2.21/1.26  Total                : 0.53
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
