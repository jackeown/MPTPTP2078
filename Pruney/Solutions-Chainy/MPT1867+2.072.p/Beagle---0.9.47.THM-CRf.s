%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:32 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 157 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 322 expanded)
%              Number of equality atoms :   25 (  65 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_262,plain,(
    ! [A_76,B_77] :
      ( r1_tarski('#skF_2'(A_76,B_77),B_77)
      | v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_283,plain,(
    ! [A_80] :
      ( r1_tarski('#skF_2'(A_80,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_50,c_262])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_8])).

tff(c_288,plain,(
    ! [A_81] :
      ( '#skF_2'(A_81,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_283,c_63])).

tff(c_291,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_288,c_32])).

tff(c_294,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_291])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_227,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tops_1(A_69,B_70),B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_232,plain,(
    ! [A_71] :
      ( r1_tarski(k1_tops_1(A_71,'#skF_4'),'#skF_4')
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_50,c_227])).

tff(c_242,plain,(
    ! [A_74] :
      ( k1_tops_1(A_74,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_232,c_63])).

tff(c_246,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_242])).

tff(c_237,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k1_tops_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_256,plain,(
    ! [A_75] :
      ( v3_pre_topc(k1_tops_1(A_75,'#skF_4'),A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_50,c_237])).

tff(c_259,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_256])).

tff(c_261,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_259])).

tff(c_86,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_50,B_51] : r1_tarski(k3_xboole_0(A_50,B_51),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [B_51] : k3_xboole_0('#skF_4',B_51) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_65,c_63])).

tff(c_102,plain,(
    ! [B_53] : k3_xboole_0(B_53,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_70])).

tff(c_215,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_217,plain,(
    ! [A_10,B_65] : k9_subset_1(A_10,B_65,'#skF_4') = k3_xboole_0(B_65,'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_215])).

tff(c_219,plain,(
    ! [A_10,B_65] : k9_subset_1(A_10,B_65,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_217])).

tff(c_411,plain,(
    ! [A_105,B_106,D_107] :
      ( k9_subset_1(u1_struct_0(A_105),B_106,D_107) != '#skF_2'(A_105,B_106)
      | ~ v3_pre_topc(D_107,A_105)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_416,plain,(
    ! [A_105,B_65] :
      ( '#skF_2'(A_105,B_65) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_105)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_105)))
      | v2_tex_2(B_65,A_105)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_411])).

tff(c_419,plain,(
    ! [A_108,B_109] :
      ( '#skF_2'(A_108,B_109) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_108)
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_416])).

tff(c_433,plain,(
    ! [A_110] :
      ( '#skF_2'(A_110,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_110)
      | v2_tex_2('#skF_4',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_50,c_419])).

tff(c_436,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_261,c_433])).

tff(c_439,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_294,c_436])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n019.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.38  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.65/1.38  
% 2.65/1.38  %Foreground sorts:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Background operators:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Foreground operators:
% 2.65/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.65/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.65/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.38  
% 2.65/1.40  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.65/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.65/1.40  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.65/1.40  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.65/1.40  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.65/1.40  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.65/1.40  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.65/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.65/1.40  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.65/1.40  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_44, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.40  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.65/1.40  tff(c_12, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.40  tff(c_50, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 2.65/1.40  tff(c_262, plain, (![A_76, B_77]: (r1_tarski('#skF_2'(A_76, B_77), B_77) | v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.40  tff(c_283, plain, (![A_80]: (r1_tarski('#skF_2'(A_80, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_50, c_262])).
% 2.65/1.40  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.40  tff(c_63, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_8])).
% 2.65/1.40  tff(c_288, plain, (![A_81]: ('#skF_2'(A_81, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_283, c_63])).
% 2.65/1.40  tff(c_291, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_288, c_32])).
% 2.65/1.40  tff(c_294, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_291])).
% 2.65/1.40  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.65/1.40  tff(c_227, plain, (![A_69, B_70]: (r1_tarski(k1_tops_1(A_69, B_70), B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.40  tff(c_232, plain, (![A_71]: (r1_tarski(k1_tops_1(A_71, '#skF_4'), '#skF_4') | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_50, c_227])).
% 2.65/1.40  tff(c_242, plain, (![A_74]: (k1_tops_1(A_74, '#skF_4')='#skF_4' | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_232, c_63])).
% 2.65/1.40  tff(c_246, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_242])).
% 2.65/1.40  tff(c_237, plain, (![A_72, B_73]: (v3_pre_topc(k1_tops_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.40  tff(c_256, plain, (![A_75]: (v3_pre_topc(k1_tops_1(A_75, '#skF_4'), A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(resolution, [status(thm)], [c_50, c_237])).
% 2.65/1.40  tff(c_259, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_246, c_256])).
% 2.65/1.40  tff(c_261, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_259])).
% 2.65/1.40  tff(c_86, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.40  tff(c_65, plain, (![A_50, B_51]: (r1_tarski(k3_xboole_0(A_50, B_51), A_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.40  tff(c_70, plain, (![B_51]: (k3_xboole_0('#skF_4', B_51)='#skF_4')), inference(resolution, [status(thm)], [c_65, c_63])).
% 2.65/1.40  tff(c_102, plain, (![B_53]: (k3_xboole_0(B_53, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_86, c_70])).
% 2.65/1.40  tff(c_215, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.40  tff(c_217, plain, (![A_10, B_65]: (k9_subset_1(A_10, B_65, '#skF_4')=k3_xboole_0(B_65, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_215])).
% 2.65/1.40  tff(c_219, plain, (![A_10, B_65]: (k9_subset_1(A_10, B_65, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_217])).
% 2.65/1.40  tff(c_411, plain, (![A_105, B_106, D_107]: (k9_subset_1(u1_struct_0(A_105), B_106, D_107)!='#skF_2'(A_105, B_106) | ~v3_pre_topc(D_107, A_105) | ~m1_subset_1(D_107, k1_zfmisc_1(u1_struct_0(A_105))) | v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.40  tff(c_416, plain, (![A_105, B_65]: ('#skF_2'(A_105, B_65)!='#skF_4' | ~v3_pre_topc('#skF_4', A_105) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_105))) | v2_tex_2(B_65, A_105) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_219, c_411])).
% 2.65/1.40  tff(c_419, plain, (![A_108, B_109]: ('#skF_2'(A_108, B_109)!='#skF_4' | ~v3_pre_topc('#skF_4', A_108) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_416])).
% 2.65/1.40  tff(c_433, plain, (![A_110]: ('#skF_2'(A_110, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_110) | v2_tex_2('#skF_4', A_110) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_50, c_419])).
% 2.65/1.40  tff(c_436, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_261, c_433])).
% 2.65/1.40  tff(c_439, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_294, c_436])).
% 2.65/1.40  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_439])).
% 2.65/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  Inference rules
% 2.65/1.40  ----------------------
% 2.65/1.40  #Ref     : 0
% 2.65/1.40  #Sup     : 90
% 2.65/1.40  #Fact    : 0
% 2.65/1.40  #Define  : 0
% 2.65/1.40  #Split   : 0
% 2.65/1.40  #Chain   : 0
% 2.65/1.40  #Close   : 0
% 2.65/1.40  
% 2.65/1.40  Ordering : KBO
% 2.65/1.40  
% 2.65/1.40  Simplification rules
% 2.65/1.40  ----------------------
% 2.65/1.40  #Subsume      : 2
% 2.65/1.40  #Demod        : 57
% 2.65/1.40  #Tautology    : 49
% 2.65/1.40  #SimpNegUnit  : 9
% 2.65/1.40  #BackRed      : 2
% 2.65/1.40  
% 2.65/1.40  #Partial instantiations: 0
% 2.65/1.40  #Strategies tried      : 1
% 2.65/1.40  
% 2.65/1.40  Timing (in seconds)
% 2.65/1.40  ----------------------
% 2.65/1.40  Preprocessing        : 0.33
% 2.65/1.40  Parsing              : 0.18
% 2.65/1.40  CNF conversion       : 0.02
% 2.65/1.40  Main loop            : 0.26
% 2.65/1.40  Inferencing          : 0.10
% 2.65/1.40  Reduction            : 0.08
% 2.65/1.40  Demodulation         : 0.06
% 2.65/1.40  BG Simplification    : 0.02
% 2.65/1.40  Subsumption          : 0.04
% 2.65/1.40  Abstraction          : 0.02
% 2.65/1.40  MUC search           : 0.00
% 2.65/1.40  Cooper               : 0.00
% 2.65/1.40  Total                : 0.62
% 2.65/1.40  Index Insertion      : 0.00
% 2.65/1.40  Index Deletion       : 0.00
% 2.65/1.40  Index Matching       : 0.00
% 2.65/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
