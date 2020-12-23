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
% DateTime   : Thu Dec  3 10:23:51 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   63 (  98 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 262 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_5',u1_pre_topc('#skF_4'))
    | ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_39,plain,(
    ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,
    ( v1_tops_2('#skF_5','#skF_4')
    | r1_tarski('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    r1_tarski('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_38])).

tff(c_81,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50,B_51),B_51)
      | v1_tops_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50))))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_89,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_85])).

tff(c_90,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_89])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_2)
      | ~ r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_198,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1('#skF_3'(A_81,B_82),k1_zfmisc_1(u1_struct_0(A_81)))
      | v1_tops_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81))))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( v3_pre_topc(B_15,A_13)
      | ~ r2_hidden(B_15,u1_pre_topc(A_13))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_296,plain,(
    ! [A_102,B_103] :
      ( v3_pre_topc('#skF_3'(A_102,B_103),A_102)
      | ~ r2_hidden('#skF_3'(A_102,B_103),u1_pre_topc(A_102))
      | v1_tops_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_102))))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_198,c_14])).

tff(c_315,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4')
    | ~ r1_tarski('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_93,c_296])).

tff(c_334,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_28,c_315])).

tff(c_335,plain,(
    v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_334])).

tff(c_22,plain,(
    ! [A_17,B_23] :
      ( ~ v3_pre_topc('#skF_3'(A_17,B_23),A_17)
      | v1_tops_2(B_23,A_17)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_337,plain,
    ( v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_335,c_22])).

tff(c_340,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_340])).

tff(c_343,plain,(
    ~ r1_tarski('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_344,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_6,B_7,C_11] :
      ( m1_subset_1('#skF_2'(A_6,B_7,C_11),A_6)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_6,B_7,C_11] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_11),B_7)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_428,plain,(
    ! [C_142,A_143,B_144] :
      ( v3_pre_topc(C_142,A_143)
      | ~ r2_hidden(C_142,B_144)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ v1_tops_2(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143))))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_531,plain,(
    ! [A_183,B_184,C_185,A_186] :
      ( v3_pre_topc('#skF_2'(A_183,B_184,C_185),A_186)
      | ~ m1_subset_1('#skF_2'(A_183,B_184,C_185),k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ v1_tops_2(B_184,A_186)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_186))))
      | ~ l1_pre_topc(A_186)
      | r1_tarski(B_184,C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_10,c_428])).

tff(c_544,plain,(
    ! [A_190,B_191,C_192] :
      ( v3_pre_topc('#skF_2'(k1_zfmisc_1(u1_struct_0(A_190)),B_191,C_192),A_190)
      | ~ v1_tops_2(B_191,A_190)
      | ~ l1_pre_topc(A_190)
      | r1_tarski(B_191,C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190))))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190)))) ) ),
    inference(resolution,[status(thm)],[c_12,c_531])).

tff(c_404,plain,(
    ! [A_137,B_138,C_139] :
      ( m1_subset_1('#skF_2'(A_137,B_138,C_139),A_137)
      | r1_tarski(B_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( r2_hidden(B_15,u1_pre_topc(A_13))
      | ~ v3_pre_topc(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_503,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_hidden('#skF_2'(k1_zfmisc_1(u1_struct_0(A_178)),B_179,C_180),u1_pre_topc(A_178))
      | ~ v3_pre_topc('#skF_2'(k1_zfmisc_1(u1_struct_0(A_178)),B_179,C_180),A_178)
      | ~ l1_pre_topc(A_178)
      | r1_tarski(B_179,C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178))))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))) ) ),
    inference(resolution,[status(thm)],[c_404,c_16])).

tff(c_8,plain,(
    ! [A_6,B_7,C_11] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_11),C_11)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_517,plain,(
    ! [A_178,B_179] :
      ( ~ v3_pre_topc('#skF_2'(k1_zfmisc_1(u1_struct_0(A_178)),B_179,u1_pre_topc(A_178)),A_178)
      | ~ l1_pre_topc(A_178)
      | r1_tarski(B_179,u1_pre_topc(A_178))
      | ~ m1_subset_1(u1_pre_topc(A_178),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178))))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))) ) ),
    inference(resolution,[status(thm)],[c_503,c_8])).

tff(c_550,plain,(
    ! [B_193,A_194] :
      ( ~ v1_tops_2(B_193,A_194)
      | ~ l1_pre_topc(A_194)
      | r1_tarski(B_193,u1_pre_topc(A_194))
      | ~ m1_subset_1(u1_pre_topc(A_194),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_194))))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_194)))) ) ),
    inference(resolution,[status(thm)],[c_544,c_517])).

tff(c_554,plain,(
    ! [B_195,A_196] :
      ( ~ v1_tops_2(B_195,A_196)
      | r1_tarski(B_195,u1_pre_topc(A_196))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_196))))
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_18,c_550])).

tff(c_564,plain,
    ( ~ v1_tops_2('#skF_5','#skF_4')
    | r1_tarski('#skF_5',u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_554])).

tff(c_570,plain,(
    r1_tarski('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_344,c_564])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.77/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.77/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.77/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.42  
% 2.77/1.44  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 2.77/1.44  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 2.77/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.44  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.77/1.44  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.77/1.44  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.77/1.44  tff(c_32, plain, (~r1_tarski('#skF_5', u1_pre_topc('#skF_4')) | ~v1_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.44  tff(c_39, plain, (~v1_tops_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 2.77/1.44  tff(c_30, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.44  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.44  tff(c_38, plain, (v1_tops_2('#skF_5', '#skF_4') | r1_tarski('#skF_5', u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.44  tff(c_40, plain, (r1_tarski('#skF_5', u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_39, c_38])).
% 2.77/1.44  tff(c_81, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50, B_51), B_51) | v1_tops_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50)))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.44  tff(c_85, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.77/1.44  tff(c_89, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_85])).
% 2.77/1.44  tff(c_90, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_39, c_89])).
% 2.77/1.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.44  tff(c_93, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_2) | ~r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.77/1.44  tff(c_198, plain, (![A_81, B_82]: (m1_subset_1('#skF_3'(A_81, B_82), k1_zfmisc_1(u1_struct_0(A_81))) | v1_tops_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81)))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.44  tff(c_14, plain, (![B_15, A_13]: (v3_pre_topc(B_15, A_13) | ~r2_hidden(B_15, u1_pre_topc(A_13)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.44  tff(c_296, plain, (![A_102, B_103]: (v3_pre_topc('#skF_3'(A_102, B_103), A_102) | ~r2_hidden('#skF_3'(A_102, B_103), u1_pre_topc(A_102)) | v1_tops_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_102)))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_198, c_14])).
% 2.77/1.44  tff(c_315, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_5', u1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_93, c_296])).
% 2.77/1.44  tff(c_334, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_28, c_315])).
% 2.77/1.44  tff(c_335, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_39, c_334])).
% 2.77/1.44  tff(c_22, plain, (![A_17, B_23]: (~v3_pre_topc('#skF_3'(A_17, B_23), A_17) | v1_tops_2(B_23, A_17) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.44  tff(c_337, plain, (v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_335, c_22])).
% 2.77/1.44  tff(c_340, plain, (v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_337])).
% 2.77/1.44  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_340])).
% 2.77/1.44  tff(c_343, plain, (~r1_tarski('#skF_5', u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_32])).
% 2.77/1.44  tff(c_344, plain, (v1_tops_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.77/1.44  tff(c_18, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.44  tff(c_12, plain, (![A_6, B_7, C_11]: (m1_subset_1('#skF_2'(A_6, B_7, C_11), A_6) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.44  tff(c_10, plain, (![A_6, B_7, C_11]: (r2_hidden('#skF_2'(A_6, B_7, C_11), B_7) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.44  tff(c_428, plain, (![C_142, A_143, B_144]: (v3_pre_topc(C_142, A_143) | ~r2_hidden(C_142, B_144) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~v1_tops_2(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.44  tff(c_531, plain, (![A_183, B_184, C_185, A_186]: (v3_pre_topc('#skF_2'(A_183, B_184, C_185), A_186) | ~m1_subset_1('#skF_2'(A_183, B_184, C_185), k1_zfmisc_1(u1_struct_0(A_186))) | ~v1_tops_2(B_184, A_186) | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_186)))) | ~l1_pre_topc(A_186) | r1_tarski(B_184, C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(A_183)) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(resolution, [status(thm)], [c_10, c_428])).
% 2.77/1.44  tff(c_544, plain, (![A_190, B_191, C_192]: (v3_pre_topc('#skF_2'(k1_zfmisc_1(u1_struct_0(A_190)), B_191, C_192), A_190) | ~v1_tops_2(B_191, A_190) | ~l1_pre_topc(A_190) | r1_tarski(B_191, C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190)))) | ~m1_subset_1(B_191, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190)))))), inference(resolution, [status(thm)], [c_12, c_531])).
% 2.77/1.44  tff(c_404, plain, (![A_137, B_138, C_139]: (m1_subset_1('#skF_2'(A_137, B_138, C_139), A_137) | r1_tarski(B_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.44  tff(c_16, plain, (![B_15, A_13]: (r2_hidden(B_15, u1_pre_topc(A_13)) | ~v3_pre_topc(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.44  tff(c_503, plain, (![A_178, B_179, C_180]: (r2_hidden('#skF_2'(k1_zfmisc_1(u1_struct_0(A_178)), B_179, C_180), u1_pre_topc(A_178)) | ~v3_pre_topc('#skF_2'(k1_zfmisc_1(u1_struct_0(A_178)), B_179, C_180), A_178) | ~l1_pre_topc(A_178) | r1_tarski(B_179, C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))) | ~m1_subset_1(B_179, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))))), inference(resolution, [status(thm)], [c_404, c_16])).
% 2.77/1.44  tff(c_8, plain, (![A_6, B_7, C_11]: (~r2_hidden('#skF_2'(A_6, B_7, C_11), C_11) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.44  tff(c_517, plain, (![A_178, B_179]: (~v3_pre_topc('#skF_2'(k1_zfmisc_1(u1_struct_0(A_178)), B_179, u1_pre_topc(A_178)), A_178) | ~l1_pre_topc(A_178) | r1_tarski(B_179, u1_pre_topc(A_178)) | ~m1_subset_1(u1_pre_topc(A_178), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))) | ~m1_subset_1(B_179, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))))), inference(resolution, [status(thm)], [c_503, c_8])).
% 2.77/1.44  tff(c_550, plain, (![B_193, A_194]: (~v1_tops_2(B_193, A_194) | ~l1_pre_topc(A_194) | r1_tarski(B_193, u1_pre_topc(A_194)) | ~m1_subset_1(u1_pre_topc(A_194), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_194)))) | ~m1_subset_1(B_193, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_194)))))), inference(resolution, [status(thm)], [c_544, c_517])).
% 2.77/1.44  tff(c_554, plain, (![B_195, A_196]: (~v1_tops_2(B_195, A_196) | r1_tarski(B_195, u1_pre_topc(A_196)) | ~m1_subset_1(B_195, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_196)))) | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_18, c_550])).
% 2.77/1.44  tff(c_564, plain, (~v1_tops_2('#skF_5', '#skF_4') | r1_tarski('#skF_5', u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_554])).
% 2.77/1.44  tff(c_570, plain, (r1_tarski('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_344, c_564])).
% 2.77/1.44  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_570])).
% 2.77/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  Inference rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Ref     : 0
% 2.77/1.44  #Sup     : 118
% 2.77/1.44  #Fact    : 0
% 2.77/1.44  #Define  : 0
% 2.77/1.44  #Split   : 2
% 2.77/1.44  #Chain   : 0
% 2.77/1.44  #Close   : 0
% 2.77/1.44  
% 2.77/1.44  Ordering : KBO
% 2.77/1.44  
% 2.77/1.44  Simplification rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Subsume      : 29
% 2.77/1.44  #Demod        : 27
% 2.77/1.44  #Tautology    : 17
% 2.77/1.44  #SimpNegUnit  : 8
% 2.77/1.44  #BackRed      : 0
% 2.77/1.44  
% 2.77/1.44  #Partial instantiations: 0
% 2.77/1.44  #Strategies tried      : 1
% 2.77/1.44  
% 2.77/1.44  Timing (in seconds)
% 2.77/1.44  ----------------------
% 2.77/1.44  Preprocessing        : 0.30
% 2.77/1.44  Parsing              : 0.17
% 2.77/1.44  CNF conversion       : 0.02
% 2.77/1.44  Main loop            : 0.38
% 2.77/1.44  Inferencing          : 0.15
% 2.77/1.44  Reduction            : 0.09
% 2.77/1.44  Demodulation         : 0.06
% 2.77/1.44  BG Simplification    : 0.02
% 2.77/1.44  Subsumption          : 0.09
% 2.77/1.44  Abstraction          : 0.02
% 2.77/1.44  MUC search           : 0.00
% 2.77/1.44  Cooper               : 0.00
% 2.77/1.44  Total                : 0.71
% 2.77/1.44  Index Insertion      : 0.00
% 2.77/1.44  Index Deletion       : 0.00
% 2.77/1.44  Index Matching       : 0.00
% 2.77/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
