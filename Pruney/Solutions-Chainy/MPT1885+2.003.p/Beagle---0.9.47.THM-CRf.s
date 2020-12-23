%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 303 expanded)
%              Number of leaves         :   26 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 (1558 expanded)
%              Number of equality atoms :   24 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    ! [B_33,A_34] :
      ( v2_tex_2(B_33,A_34)
      | ~ v3_tex_2(B_33,A_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_52,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_49])).

tff(c_110,plain,(
    ! [A_50,B_51] :
      ( ~ v2_struct_0('#skF_3'(A_50,B_51))
      | ~ v2_tex_2(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | v1_xboole_0(B_51)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_116,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_110])).

tff(c_120,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_52,c_116])).

tff(c_121,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_120])).

tff(c_98,plain,(
    ! [A_48,B_49] :
      ( v1_pre_topc('#skF_3'(A_48,B_49))
      | ~ v2_tex_2(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | v1_xboole_0(B_49)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_104,plain,
    ( v1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_108,plain,
    ( v1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_52,c_104])).

tff(c_109,plain,(
    v1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_108])).

tff(c_162,plain,(
    ! [A_58,B_59] :
      ( m1_pre_topc('#skF_3'(A_58,B_59),A_58)
      | ~ v2_tex_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_xboole_0(B_59)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_168,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_162])).

tff(c_173,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_52,c_168])).

tff(c_174,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_173])).

tff(c_175,plain,(
    ! [A_60,B_61] :
      ( u1_struct_0('#skF_3'(A_60,B_61)) = B_61
      | ~ v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(B_61)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_184,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_175])).

tff(c_189,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_52,c_184])).

tff(c_190,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_189])).

tff(c_54,plain,(
    ! [B_37,A_38] :
      ( u1_struct_0(B_37) = '#skF_2'(A_38,B_37)
      | v4_tex_2(B_37,A_38)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [C_31] :
      ( u1_struct_0(C_31) != '#skF_5'
      | ~ v4_tex_2(C_31,'#skF_4')
      | ~ m1_pre_topc(C_31,'#skF_4')
      | ~ v1_pre_topc(C_31)
      | v2_struct_0(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    ! [B_37] :
      ( u1_struct_0(B_37) != '#skF_5'
      | ~ v1_pre_topc(B_37)
      | v2_struct_0(B_37)
      | u1_struct_0(B_37) = '#skF_2'('#skF_4',B_37)
      | ~ m1_pre_topc(B_37,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_32])).

tff(c_61,plain,(
    ! [B_37] :
      ( u1_struct_0(B_37) != '#skF_5'
      | ~ v1_pre_topc(B_37)
      | v2_struct_0(B_37)
      | u1_struct_0(B_37) = '#skF_2'('#skF_4',B_37)
      | ~ m1_pre_topc(B_37,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58])).

tff(c_62,plain,(
    ! [B_37] :
      ( u1_struct_0(B_37) != '#skF_5'
      | ~ v1_pre_topc(B_37)
      | v2_struct_0(B_37)
      | u1_struct_0(B_37) = '#skF_2'('#skF_4',B_37)
      | ~ m1_pre_topc(B_37,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_61])).

tff(c_193,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) != '#skF_5'
    | ~ v1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_2'('#skF_4','#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_174,c_62])).

tff(c_196,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) != '#skF_5'
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_2'('#skF_4','#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_193])).

tff(c_197,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) != '#skF_5'
    | u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_2'('#skF_4','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_196])).

tff(c_248,plain,(
    '#skF_2'('#skF_4','#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_190,c_197])).

tff(c_16,plain,(
    ! [A_11,B_17] :
      ( ~ v3_tex_2('#skF_2'(A_11,B_17),A_11)
      | v4_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_255,plain,
    ( ~ v3_tex_2('#skF_5','#skF_4')
    | v4_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_16])).

tff(c_262,plain,
    ( v4_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_174,c_34,c_255])).

tff(c_263,plain,(
    v4_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_262])).

tff(c_267,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) != '#skF_5'
    | ~ m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_263,c_32])).

tff(c_270,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_174,c_190,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.39  
% 2.46/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.39  %$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.46/1.39  
% 2.46/1.39  %Foreground sorts:
% 2.46/1.39  
% 2.46/1.39  
% 2.46/1.39  %Background operators:
% 2.46/1.39  
% 2.46/1.39  
% 2.46/1.39  %Foreground operators:
% 2.46/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.39  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.46/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.46/1.39  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.46/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.46/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.46/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.46/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.46/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.46/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.46/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.46/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.39  
% 2.46/1.40  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_tex_2)).
% 2.46/1.40  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.46/1.40  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 2.46/1.40  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 2.46/1.40  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_38, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_34, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_46, plain, (![B_33, A_34]: (v2_tex_2(B_33, A_34) | ~v3_tex_2(B_33, A_34) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.40  tff(c_49, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_46])).
% 2.46/1.40  tff(c_52, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_49])).
% 2.46/1.40  tff(c_110, plain, (![A_50, B_51]: (~v2_struct_0('#skF_3'(A_50, B_51)) | ~v2_tex_2(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | v1_xboole_0(B_51) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.46/1.40  tff(c_116, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_110])).
% 2.46/1.40  tff(c_120, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_52, c_116])).
% 2.46/1.40  tff(c_121, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_120])).
% 2.46/1.40  tff(c_98, plain, (![A_48, B_49]: (v1_pre_topc('#skF_3'(A_48, B_49)) | ~v2_tex_2(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | v1_xboole_0(B_49) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.46/1.40  tff(c_104, plain, (v1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_98])).
% 2.46/1.40  tff(c_108, plain, (v1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_52, c_104])).
% 2.46/1.40  tff(c_109, plain, (v1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_108])).
% 2.46/1.40  tff(c_162, plain, (![A_58, B_59]: (m1_pre_topc('#skF_3'(A_58, B_59), A_58) | ~v2_tex_2(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | v1_xboole_0(B_59) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.46/1.40  tff(c_168, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_162])).
% 2.46/1.40  tff(c_173, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_52, c_168])).
% 2.46/1.40  tff(c_174, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_173])).
% 2.46/1.40  tff(c_175, plain, (![A_60, B_61]: (u1_struct_0('#skF_3'(A_60, B_61))=B_61 | ~v2_tex_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(B_61) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.46/1.40  tff(c_184, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_175])).
% 2.46/1.40  tff(c_189, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_52, c_184])).
% 2.46/1.40  tff(c_190, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_189])).
% 2.46/1.40  tff(c_54, plain, (![B_37, A_38]: (u1_struct_0(B_37)='#skF_2'(A_38, B_37) | v4_tex_2(B_37, A_38) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.40  tff(c_32, plain, (![C_31]: (u1_struct_0(C_31)!='#skF_5' | ~v4_tex_2(C_31, '#skF_4') | ~m1_pre_topc(C_31, '#skF_4') | ~v1_pre_topc(C_31) | v2_struct_0(C_31))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.46/1.40  tff(c_58, plain, (![B_37]: (u1_struct_0(B_37)!='#skF_5' | ~v1_pre_topc(B_37) | v2_struct_0(B_37) | u1_struct_0(B_37)='#skF_2'('#skF_4', B_37) | ~m1_pre_topc(B_37, '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_32])).
% 2.46/1.40  tff(c_61, plain, (![B_37]: (u1_struct_0(B_37)!='#skF_5' | ~v1_pre_topc(B_37) | v2_struct_0(B_37) | u1_struct_0(B_37)='#skF_2'('#skF_4', B_37) | ~m1_pre_topc(B_37, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58])).
% 2.46/1.40  tff(c_62, plain, (![B_37]: (u1_struct_0(B_37)!='#skF_5' | ~v1_pre_topc(B_37) | v2_struct_0(B_37) | u1_struct_0(B_37)='#skF_2'('#skF_4', B_37) | ~m1_pre_topc(B_37, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_61])).
% 2.46/1.40  tff(c_193, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))!='#skF_5' | ~v1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_2'('#skF_4', '#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_174, c_62])).
% 2.46/1.40  tff(c_196, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))!='#skF_5' | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_2'('#skF_4', '#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_193])).
% 2.46/1.40  tff(c_197, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))!='#skF_5' | u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_2'('#skF_4', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_121, c_196])).
% 2.46/1.40  tff(c_248, plain, ('#skF_2'('#skF_4', '#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_190, c_197])).
% 2.46/1.40  tff(c_16, plain, (![A_11, B_17]: (~v3_tex_2('#skF_2'(A_11, B_17), A_11) | v4_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.40  tff(c_255, plain, (~v3_tex_2('#skF_5', '#skF_4') | v4_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_248, c_16])).
% 2.46/1.40  tff(c_262, plain, (v4_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_174, c_34, c_255])).
% 2.46/1.40  tff(c_263, plain, (v4_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_262])).
% 2.46/1.40  tff(c_267, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))!='#skF_5' | ~m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_263, c_32])).
% 2.46/1.40  tff(c_270, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_174, c_190, c_267])).
% 2.46/1.40  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_270])).
% 2.46/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.40  
% 2.46/1.40  Inference rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Ref     : 0
% 2.46/1.40  #Sup     : 49
% 2.46/1.40  #Fact    : 0
% 2.46/1.40  #Define  : 0
% 2.46/1.40  #Split   : 0
% 2.46/1.40  #Chain   : 0
% 2.46/1.40  #Close   : 0
% 2.46/1.40  
% 2.46/1.40  Ordering : KBO
% 2.46/1.40  
% 2.46/1.40  Simplification rules
% 2.46/1.40  ----------------------
% 2.46/1.40  #Subsume      : 2
% 2.46/1.40  #Demod        : 41
% 2.46/1.40  #Tautology    : 8
% 2.46/1.40  #SimpNegUnit  : 17
% 2.46/1.40  #BackRed      : 0
% 2.46/1.40  
% 2.46/1.40  #Partial instantiations: 0
% 2.46/1.40  #Strategies tried      : 1
% 2.46/1.40  
% 2.46/1.40  Timing (in seconds)
% 2.46/1.40  ----------------------
% 2.46/1.41  Preprocessing        : 0.32
% 2.46/1.41  Parsing              : 0.17
% 2.46/1.41  CNF conversion       : 0.02
% 2.46/1.41  Main loop            : 0.21
% 2.46/1.41  Inferencing          : 0.07
% 2.46/1.41  Reduction            : 0.07
% 2.46/1.41  Demodulation         : 0.05
% 2.46/1.41  BG Simplification    : 0.02
% 2.46/1.41  Subsumption          : 0.04
% 2.46/1.41  Abstraction          : 0.01
% 2.46/1.41  MUC search           : 0.00
% 2.46/1.41  Cooper               : 0.00
% 2.46/1.41  Total                : 0.57
% 2.46/1.41  Index Insertion      : 0.00
% 2.56/1.41  Index Deletion       : 0.00
% 2.56/1.41  Index Matching       : 0.00
% 2.56/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
