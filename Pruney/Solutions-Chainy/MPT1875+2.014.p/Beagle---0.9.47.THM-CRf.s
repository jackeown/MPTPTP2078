%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   59 (  81 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 161 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_30,plain,(
    ! [A_16] :
      ( v2_tex_2(u1_struct_0(A_16),A_16)
      | ~ v1_tdlat_3(A_16)
      | ~ m1_subset_1(u1_struct_0(A_16),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_51,plain,(
    ! [A_16] :
      ( v2_tex_2(u1_struct_0(A_16),A_16)
      | ~ v1_tdlat_3(A_16)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_30])).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(A_48,A_49)
      | v1_xboole_0(k1_zfmisc_1(A_49))
      | ~ m1_subset_1(A_48,k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_93,c_12])).

tff(c_121,plain,
    ( r1_tarski('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_124,plain,(
    v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_70,plain,(
    ! [C_33,A_34] :
      ( r2_hidden(C_33,k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_33,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_34,C_33] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_33,A_34) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_128,plain,(
    ! [C_50] : ~ r1_tarski(C_50,u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_124,c_74])).

tff(c_139,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_128])).

tff(c_140,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_185,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_tex_2(C_64,A_65)
      | ~ v2_tex_2(B_66,A_65)
      | ~ r1_tarski(C_64,B_66)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_231,plain,(
    ! [A_73] :
      ( v2_tex_2('#skF_5',A_73)
      | ~ v2_tex_2(u1_struct_0('#skF_4'),A_73)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_140,c_185])).

tff(c_235,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_231])).

tff(c_238,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_235])).

tff(c_239,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_238])).

tff(c_242,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_51,c_239])).

tff(c_245,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.27  
% 2.36/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.27  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.36/1.27  
% 2.36/1.27  %Foreground sorts:
% 2.36/1.27  
% 2.36/1.27  
% 2.36/1.27  %Background operators:
% 2.36/1.27  
% 2.36/1.27  
% 2.36/1.27  %Foreground operators:
% 2.36/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.36/1.27  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.36/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.36/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.36/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.36/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.27  
% 2.36/1.28  tff(f_97, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 2.36/1.28  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.36/1.28  tff(f_48, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.36/1.28  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 2.36/1.28  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.28  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.36/1.28  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.36/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.36/1.28  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 2.36/1.28  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.36/1.28  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.36/1.28  tff(c_42, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.36/1.28  tff(c_24, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.28  tff(c_26, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.28  tff(c_47, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.36/1.28  tff(c_30, plain, (![A_16]: (v2_tex_2(u1_struct_0(A_16), A_16) | ~v1_tdlat_3(A_16) | ~m1_subset_1(u1_struct_0(A_16), k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.28  tff(c_51, plain, (![A_16]: (v2_tex_2(u1_struct_0(A_16), A_16) | ~v1_tdlat_3(A_16) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_30])).
% 2.36/1.28  tff(c_36, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.36/1.28  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.36/1.28  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.28  tff(c_93, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.28  tff(c_12, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.28  tff(c_114, plain, (![A_48, A_49]: (r1_tarski(A_48, A_49) | v1_xboole_0(k1_zfmisc_1(A_49)) | ~m1_subset_1(A_48, k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_93, c_12])).
% 2.36/1.28  tff(c_121, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4')) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_114])).
% 2.36/1.28  tff(c_124, plain, (v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_121])).
% 2.36/1.28  tff(c_70, plain, (![C_33, A_34]: (r2_hidden(C_33, k1_zfmisc_1(A_34)) | ~r1_tarski(C_33, A_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.28  tff(c_74, plain, (![A_34, C_33]: (~v1_xboole_0(k1_zfmisc_1(A_34)) | ~r1_tarski(C_33, A_34))), inference(resolution, [status(thm)], [c_70, c_2])).
% 2.36/1.28  tff(c_128, plain, (![C_50]: (~r1_tarski(C_50, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_124, c_74])).
% 2.36/1.28  tff(c_139, plain, $false, inference(resolution, [status(thm)], [c_10, c_128])).
% 2.36/1.28  tff(c_140, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_121])).
% 2.36/1.28  tff(c_185, plain, (![C_64, A_65, B_66]: (v2_tex_2(C_64, A_65) | ~v2_tex_2(B_66, A_65) | ~r1_tarski(C_64, B_66) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.36/1.28  tff(c_231, plain, (![A_73]: (v2_tex_2('#skF_5', A_73) | ~v2_tex_2(u1_struct_0('#skF_4'), A_73) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_140, c_185])).
% 2.36/1.28  tff(c_235, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_47, c_231])).
% 2.36/1.28  tff(c_238, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_235])).
% 2.36/1.28  tff(c_239, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_238])).
% 2.36/1.28  tff(c_242, plain, (~v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_51, c_239])).
% 2.36/1.28  tff(c_245, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_242])).
% 2.36/1.28  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_245])).
% 2.36/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.28  
% 2.36/1.28  Inference rules
% 2.36/1.28  ----------------------
% 2.36/1.28  #Ref     : 0
% 2.36/1.28  #Sup     : 39
% 2.36/1.28  #Fact    : 0
% 2.36/1.28  #Define  : 0
% 2.36/1.28  #Split   : 2
% 2.36/1.28  #Chain   : 0
% 2.36/1.28  #Close   : 0
% 2.36/1.28  
% 2.36/1.28  Ordering : KBO
% 2.36/1.28  
% 2.36/1.28  Simplification rules
% 2.36/1.28  ----------------------
% 2.36/1.28  #Subsume      : 2
% 2.36/1.28  #Demod        : 11
% 2.36/1.29  #Tautology    : 13
% 2.36/1.29  #SimpNegUnit  : 2
% 2.36/1.29  #BackRed      : 0
% 2.36/1.29  
% 2.36/1.29  #Partial instantiations: 0
% 2.36/1.29  #Strategies tried      : 1
% 2.36/1.29  
% 2.36/1.29  Timing (in seconds)
% 2.36/1.29  ----------------------
% 2.36/1.29  Preprocessing        : 0.30
% 2.36/1.29  Parsing              : 0.16
% 2.36/1.29  CNF conversion       : 0.02
% 2.36/1.29  Main loop            : 0.22
% 2.36/1.29  Inferencing          : 0.08
% 2.36/1.29  Reduction            : 0.06
% 2.36/1.29  Demodulation         : 0.04
% 2.36/1.29  BG Simplification    : 0.01
% 2.36/1.29  Subsumption          : 0.05
% 2.36/1.29  Abstraction          : 0.01
% 2.36/1.29  MUC search           : 0.00
% 2.36/1.29  Cooper               : 0.00
% 2.36/1.29  Total                : 0.55
% 2.36/1.29  Index Insertion      : 0.00
% 2.36/1.29  Index Deletion       : 0.00
% 2.36/1.29  Index Matching       : 0.00
% 2.36/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
