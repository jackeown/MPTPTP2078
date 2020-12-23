%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:57 EST 2020

% Result     : Theorem 8.34s
% Output     : CNFRefutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 194 expanded)
%              Number of leaves         :   27 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  152 ( 584 expanded)
%              Number of equality atoms :    6 (  43 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_155,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(A_55,B_56,C_57) = k3_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [B_56] : k9_subset_1(u1_struct_0('#skF_1'),B_56,'#skF_3') = k3_xboole_0(B_56,'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_26,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_165,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_26])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_276,plain,(
    ! [B_72,A_73] :
      ( v4_pre_topc(B_72,A_73)
      | ~ v2_compts_1(B_72,A_73)
      | ~ v8_pre_topc(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_293,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_276])).

tff(c_304,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_30,c_293])).

tff(c_28,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_290,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_276])).

tff(c_301,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_28,c_290])).

tff(c_622,plain,(
    ! [A_103,B_104,C_105] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_103),B_104,C_105),A_103)
      | ~ v4_pre_topc(C_105,A_103)
      | ~ v4_pre_topc(B_104,A_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_641,plain,(
    ! [B_56] :
      ( v4_pre_topc(k3_xboole_0(B_56,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_56,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_622])).

tff(c_865,plain,(
    ! [B_128] :
      ( v4_pre_topc(k3_xboole_0(B_128,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_301,c_641])).

tff(c_895,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_865])).

tff(c_908,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_895])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k9_subset_1(A_67,B_68,C_69),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_243,plain,(
    ! [B_56] :
      ( m1_subset_1(k3_xboole_0(B_56,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_229])).

tff(c_249,plain,(
    ! [B_56] : m1_subset_1(k3_xboole_0(B_56,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_243])).

tff(c_202,plain,(
    ! [B_62,B_63,A_64] :
      ( k9_subset_1(B_62,B_63,A_64) = k3_xboole_0(B_63,A_64)
      | ~ r1_tarski(A_64,B_62) ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_219,plain,(
    ! [B_2,B_63] : k9_subset_1(B_2,B_63,B_2) = k3_xboole_0(B_63,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k9_subset_1(A_67,B_68,C_69),A_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_229,c_16])).

tff(c_461,plain,(
    ! [C_87,A_88,B_89] :
      ( v2_compts_1(C_87,A_88)
      | ~ v4_pre_topc(C_87,A_88)
      | ~ r1_tarski(C_87,B_89)
      | ~ v2_compts_1(B_89,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2551,plain,(
    ! [A_259,B_260,C_261,A_262] :
      ( v2_compts_1(k9_subset_1(A_259,B_260,C_261),A_262)
      | ~ v4_pre_topc(k9_subset_1(A_259,B_260,C_261),A_262)
      | ~ v2_compts_1(A_259,A_262)
      | ~ m1_subset_1(k9_subset_1(A_259,B_260,C_261),k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_subset_1(A_259,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(A_259)) ) ),
    inference(resolution,[status(thm)],[c_245,c_461])).

tff(c_2591,plain,(
    ! [B_2,B_63,A_262] :
      ( v2_compts_1(k9_subset_1(B_2,B_63,B_2),A_262)
      | ~ v4_pre_topc(k9_subset_1(B_2,B_63,B_2),A_262)
      | ~ v2_compts_1(B_2,A_262)
      | ~ m1_subset_1(k3_xboole_0(B_63,B_2),k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_2551])).

tff(c_8737,plain,(
    ! [B_612,B_613,A_614] :
      ( v2_compts_1(k3_xboole_0(B_612,B_613),A_614)
      | ~ v4_pre_topc(k3_xboole_0(B_612,B_613),A_614)
      | ~ v2_compts_1(B_613,A_614)
      | ~ m1_subset_1(k3_xboole_0(B_612,B_613),k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ m1_subset_1(B_613,k1_zfmisc_1(u1_struct_0(A_614)))
      | ~ l1_pre_topc(A_614)
      | ~ v2_pre_topc(A_614)
      | ~ m1_subset_1(B_613,k1_zfmisc_1(B_613)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_219,c_2591])).

tff(c_8775,plain,(
    ! [B_56] :
      ( v2_compts_1(k3_xboole_0(B_56,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_56,'#skF_3'),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_249,c_8737])).

tff(c_8823,plain,(
    ! [B_56] :
      ( v2_compts_1(k3_xboole_0(B_56,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_56,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_28,c_8775])).

tff(c_8828,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8823])).

tff(c_8831,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_8828])).

tff(c_8835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8831])).

tff(c_8990,plain,(
    ! [B_617] :
      ( v2_compts_1(k3_xboole_0(B_617,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_617,'#skF_3'),'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_8823])).

tff(c_9034,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_908,c_8990])).

tff(c_9065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_9034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.34/3.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.34/3.13  
% 8.34/3.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.34/3.13  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.34/3.13  
% 8.34/3.13  %Foreground sorts:
% 8.34/3.13  
% 8.34/3.13  
% 8.34/3.13  %Background operators:
% 8.34/3.13  
% 8.34/3.13  
% 8.34/3.13  %Foreground operators:
% 8.34/3.13  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 8.34/3.13  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 8.34/3.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.34/3.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.34/3.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.34/3.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.34/3.13  tff('#skF_2', type, '#skF_2': $i).
% 8.34/3.13  tff('#skF_3', type, '#skF_3': $i).
% 8.34/3.13  tff('#skF_1', type, '#skF_1': $i).
% 8.34/3.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.34/3.13  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.34/3.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.34/3.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.34/3.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.34/3.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.34/3.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.34/3.13  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.34/3.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.34/3.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.34/3.13  
% 8.34/3.15  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 8.34/3.15  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.34/3.15  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 8.34/3.15  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 8.34/3.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.34/3.15  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.34/3.15  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 8.34/3.15  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 8.34/3.15  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_155, plain, (![A_55, B_56, C_57]: (k9_subset_1(A_55, B_56, C_57)=k3_xboole_0(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.34/3.15  tff(c_163, plain, (![B_56]: (k9_subset_1(u1_struct_0('#skF_1'), B_56, '#skF_3')=k3_xboole_0(B_56, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_155])).
% 8.34/3.15  tff(c_26, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_165, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_26])).
% 8.34/3.15  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_32, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_30, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_276, plain, (![B_72, A_73]: (v4_pre_topc(B_72, A_73) | ~v2_compts_1(B_72, A_73) | ~v8_pre_topc(A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.34/3.15  tff(c_293, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_276])).
% 8.34/3.15  tff(c_304, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_30, c_293])).
% 8.34/3.15  tff(c_28, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.34/3.15  tff(c_290, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_276])).
% 8.34/3.15  tff(c_301, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_28, c_290])).
% 8.34/3.15  tff(c_622, plain, (![A_103, B_104, C_105]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_103), B_104, C_105), A_103) | ~v4_pre_topc(C_105, A_103) | ~v4_pre_topc(B_104, A_103) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.34/3.15  tff(c_641, plain, (![B_56]: (v4_pre_topc(k3_xboole_0(B_56, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_56, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_622])).
% 8.34/3.15  tff(c_865, plain, (![B_128]: (v4_pre_topc(k3_xboole_0(B_128, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_128, '#skF_1') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_301, c_641])).
% 8.34/3.15  tff(c_895, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_865])).
% 8.34/3.15  tff(c_908, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_895])).
% 8.34/3.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.34/3.15  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.34/3.15  tff(c_229, plain, (![A_67, B_68, C_69]: (m1_subset_1(k9_subset_1(A_67, B_68, C_69), k1_zfmisc_1(A_67)) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.34/3.15  tff(c_243, plain, (![B_56]: (m1_subset_1(k3_xboole_0(B_56, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_163, c_229])).
% 8.34/3.15  tff(c_249, plain, (![B_56]: (m1_subset_1(k3_xboole_0(B_56, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_243])).
% 8.34/3.15  tff(c_202, plain, (![B_62, B_63, A_64]: (k9_subset_1(B_62, B_63, A_64)=k3_xboole_0(B_63, A_64) | ~r1_tarski(A_64, B_62))), inference(resolution, [status(thm)], [c_18, c_155])).
% 8.34/3.15  tff(c_219, plain, (![B_2, B_63]: (k9_subset_1(B_2, B_63, B_2)=k3_xboole_0(B_63, B_2))), inference(resolution, [status(thm)], [c_6, c_202])).
% 8.34/3.15  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.34/3.15  tff(c_245, plain, (![A_67, B_68, C_69]: (r1_tarski(k9_subset_1(A_67, B_68, C_69), A_67) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_229, c_16])).
% 8.34/3.15  tff(c_461, plain, (![C_87, A_88, B_89]: (v2_compts_1(C_87, A_88) | ~v4_pre_topc(C_87, A_88) | ~r1_tarski(C_87, B_89) | ~v2_compts_1(B_89, A_88) | ~m1_subset_1(C_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.34/3.15  tff(c_2551, plain, (![A_259, B_260, C_261, A_262]: (v2_compts_1(k9_subset_1(A_259, B_260, C_261), A_262) | ~v4_pre_topc(k9_subset_1(A_259, B_260, C_261), A_262) | ~v2_compts_1(A_259, A_262) | ~m1_subset_1(k9_subset_1(A_259, B_260, C_261), k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_subset_1(A_259, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | ~m1_subset_1(C_261, k1_zfmisc_1(A_259)))), inference(resolution, [status(thm)], [c_245, c_461])).
% 8.34/3.15  tff(c_2591, plain, (![B_2, B_63, A_262]: (v2_compts_1(k9_subset_1(B_2, B_63, B_2), A_262) | ~v4_pre_topc(k9_subset_1(B_2, B_63, B_2), A_262) | ~v2_compts_1(B_2, A_262) | ~m1_subset_1(k3_xboole_0(B_63, B_2), k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_2551])).
% 8.34/3.15  tff(c_8737, plain, (![B_612, B_613, A_614]: (v2_compts_1(k3_xboole_0(B_612, B_613), A_614) | ~v4_pre_topc(k3_xboole_0(B_612, B_613), A_614) | ~v2_compts_1(B_613, A_614) | ~m1_subset_1(k3_xboole_0(B_612, B_613), k1_zfmisc_1(u1_struct_0(A_614))) | ~m1_subset_1(B_613, k1_zfmisc_1(u1_struct_0(A_614))) | ~l1_pre_topc(A_614) | ~v2_pre_topc(A_614) | ~m1_subset_1(B_613, k1_zfmisc_1(B_613)))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_219, c_2591])).
% 8.34/3.15  tff(c_8775, plain, (![B_56]: (v2_compts_1(k3_xboole_0(B_56, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_56, '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_249, c_8737])).
% 8.34/3.15  tff(c_8823, plain, (![B_56]: (v2_compts_1(k3_xboole_0(B_56, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_56, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_28, c_8775])).
% 8.34/3.15  tff(c_8828, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8823])).
% 8.34/3.15  tff(c_8831, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_8828])).
% 8.34/3.15  tff(c_8835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8831])).
% 8.34/3.15  tff(c_8990, plain, (![B_617]: (v2_compts_1(k3_xboole_0(B_617, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_617, '#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_8823])).
% 8.34/3.15  tff(c_9034, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_908, c_8990])).
% 8.34/3.15  tff(c_9065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_9034])).
% 8.34/3.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.34/3.15  
% 8.34/3.15  Inference rules
% 8.34/3.15  ----------------------
% 8.34/3.15  #Ref     : 0
% 8.34/3.15  #Sup     : 2147
% 8.34/3.15  #Fact    : 0
% 8.34/3.15  #Define  : 0
% 8.34/3.15  #Split   : 6
% 8.34/3.15  #Chain   : 0
% 8.34/3.15  #Close   : 0
% 8.34/3.15  
% 8.34/3.15  Ordering : KBO
% 8.34/3.15  
% 8.34/3.15  Simplification rules
% 8.34/3.15  ----------------------
% 8.34/3.15  #Subsume      : 571
% 8.34/3.15  #Demod        : 1402
% 8.34/3.15  #Tautology    : 363
% 8.34/3.15  #SimpNegUnit  : 1
% 8.34/3.15  #BackRed      : 1
% 8.34/3.15  
% 8.34/3.15  #Partial instantiations: 0
% 8.34/3.15  #Strategies tried      : 1
% 8.34/3.15  
% 8.34/3.15  Timing (in seconds)
% 8.34/3.15  ----------------------
% 8.34/3.15  Preprocessing        : 0.31
% 8.34/3.15  Parsing              : 0.16
% 8.34/3.15  CNF conversion       : 0.02
% 8.34/3.15  Main loop            : 2.08
% 8.34/3.15  Inferencing          : 0.60
% 8.34/3.15  Reduction            : 0.71
% 8.34/3.15  Demodulation         : 0.55
% 8.34/3.15  BG Simplification    : 0.06
% 8.34/3.15  Subsumption          : 0.58
% 8.34/3.15  Abstraction          : 0.10
% 8.34/3.15  MUC search           : 0.00
% 8.34/3.15  Cooper               : 0.00
% 8.34/3.15  Total                : 2.42
% 8.34/3.15  Index Insertion      : 0.00
% 8.34/3.15  Index Deletion       : 0.00
% 8.34/3.15  Index Matching       : 0.00
% 8.34/3.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
