%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 204 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_32,plain,(
    ! [A_14] :
      ( v2_tex_2(u1_struct_0(A_14),A_14)
      | ~ v1_tdlat_3(A_14)
      | ~ m1_subset_1(u1_struct_0(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,(
    ! [A_14] :
      ( v2_tex_2(u1_struct_0(A_14),A_14)
      | ~ v1_tdlat_3(A_14)
      | ~ l1_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_32])).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_68,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_82,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_93,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(A_46,A_47)
      | v1_xboole_0(k1_zfmisc_1(A_47))
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_126,plain,
    ( r1_tarski('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_133,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_126])).

tff(c_214,plain,(
    ! [C_68,A_69,B_70] :
      ( v2_tex_2(C_68,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ r1_tarski(C_68,B_70)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_272,plain,(
    ! [A_77] :
      ( v2_tex_2('#skF_4',A_77)
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_77)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_133,c_214])).

tff(c_282,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_272])).

tff(c_287,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_282])).

tff(c_288,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_287])).

tff(c_291,plain,
    ( ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_288])).

tff(c_294,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_291])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_294])).

tff(c_298,plain,(
    v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_80,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | ~ v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_49,c_68])).

tff(c_302,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_298,c_80])).

tff(c_30,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_305,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_302,c_30])).

tff(c_308,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_305])).

tff(c_311,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.37  
% 2.30/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.37  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.30/1.37  
% 2.30/1.37  %Foreground sorts:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Background operators:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Foreground operators:
% 2.30/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.37  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.30/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.30/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.30/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.30/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.37  
% 2.63/1.39  tff(f_110, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 2.63/1.39  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.63/1.39  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.63/1.39  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.63/1.39  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 2.63/1.39  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.39  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.63/1.39  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.63/1.39  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 2.63/1.39  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.63/1.39  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.63/1.39  tff(c_28, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.39  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.63/1.39  tff(c_44, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.63/1.39  tff(c_22, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.39  tff(c_24, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.39  tff(c_49, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.63/1.39  tff(c_32, plain, (![A_14]: (v2_tex_2(u1_struct_0(A_14), A_14) | ~v1_tdlat_3(A_14) | ~m1_subset_1(u1_struct_0(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.63/1.39  tff(c_53, plain, (![A_14]: (v2_tex_2(u1_struct_0(A_14), A_14) | ~v1_tdlat_3(A_14) | ~l1_pre_topc(A_14) | v2_struct_0(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_32])).
% 2.63/1.39  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.63/1.39  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.63/1.39  tff(c_68, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.39  tff(c_79, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_40, c_68])).
% 2.63/1.39  tff(c_82, plain, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_79])).
% 2.63/1.39  tff(c_93, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | v1_xboole_0(B_41) | ~m1_subset_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.39  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.39  tff(c_119, plain, (![A_46, A_47]: (r1_tarski(A_46, A_47) | v1_xboole_0(k1_zfmisc_1(A_47)) | ~m1_subset_1(A_46, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_93, c_2])).
% 2.63/1.39  tff(c_126, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_40, c_119])).
% 2.63/1.39  tff(c_133, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_82, c_126])).
% 2.63/1.39  tff(c_214, plain, (![C_68, A_69, B_70]: (v2_tex_2(C_68, A_69) | ~v2_tex_2(B_70, A_69) | ~r1_tarski(C_68, B_70) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.63/1.39  tff(c_272, plain, (![A_77]: (v2_tex_2('#skF_4', A_77) | ~v2_tex_2(u1_struct_0('#skF_3'), A_77) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_133, c_214])).
% 2.63/1.39  tff(c_282, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_49, c_272])).
% 2.63/1.39  tff(c_287, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_282])).
% 2.63/1.39  tff(c_288, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_287])).
% 2.63/1.39  tff(c_291, plain, (~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_53, c_288])).
% 2.63/1.39  tff(c_294, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_291])).
% 2.63/1.39  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_294])).
% 2.63/1.39  tff(c_298, plain, (v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_79])).
% 2.63/1.39  tff(c_80, plain, (![A_9]: (v1_xboole_0(A_9) | ~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_49, c_68])).
% 2.63/1.39  tff(c_302, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_298, c_80])).
% 2.63/1.39  tff(c_30, plain, (![A_13]: (~v1_xboole_0(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.39  tff(c_305, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_302, c_30])).
% 2.63/1.39  tff(c_308, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_305])).
% 2.63/1.39  tff(c_311, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_308])).
% 2.63/1.39  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_311])).
% 2.63/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  Inference rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Ref     : 0
% 2.63/1.39  #Sup     : 51
% 2.63/1.39  #Fact    : 0
% 2.63/1.39  #Define  : 0
% 2.63/1.39  #Split   : 1
% 2.63/1.39  #Chain   : 0
% 2.63/1.39  #Close   : 0
% 2.63/1.39  
% 2.63/1.39  Ordering : KBO
% 2.63/1.39  
% 2.63/1.39  Simplification rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Subsume      : 2
% 2.63/1.39  #Demod        : 8
% 2.63/1.39  #Tautology    : 18
% 2.63/1.39  #SimpNegUnit  : 4
% 2.63/1.39  #BackRed      : 0
% 2.63/1.39  
% 2.63/1.39  #Partial instantiations: 0
% 2.63/1.39  #Strategies tried      : 1
% 2.63/1.39  
% 2.63/1.39  Timing (in seconds)
% 2.63/1.39  ----------------------
% 2.63/1.39  Preprocessing        : 0.32
% 2.63/1.39  Parsing              : 0.18
% 2.63/1.39  CNF conversion       : 0.02
% 2.63/1.39  Main loop            : 0.25
% 2.63/1.39  Inferencing          : 0.09
% 2.63/1.39  Reduction            : 0.06
% 2.63/1.39  Demodulation         : 0.04
% 2.63/1.39  BG Simplification    : 0.02
% 2.63/1.39  Subsumption          : 0.06
% 2.63/1.39  Abstraction          : 0.01
% 2.63/1.39  MUC search           : 0.00
% 2.63/1.39  Cooper               : 0.00
% 2.63/1.39  Total                : 0.60
% 2.63/1.39  Index Insertion      : 0.00
% 2.63/1.39  Index Deletion       : 0.00
% 2.63/1.39  Index Matching       : 0.00
% 2.63/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
