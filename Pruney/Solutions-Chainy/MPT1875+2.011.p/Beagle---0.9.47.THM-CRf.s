%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 177 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 485 expanded)
%              Number of equality atoms :    5 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    ! [A_33,B_34] :
      ( u1_struct_0(k1_pre_topc(A_33,B_34)) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_56,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_53])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( v1_pre_topc(k1_pre_topc(A_1,B_2))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [B_2] :
      ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),B_2))
      | ~ m1_subset_1(B_2,k1_zfmisc_1('#skF_2'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_209,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_214,plain,(
    ! [A_55,B_56] :
      ( m1_pre_topc(k1_pre_topc(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_218,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_214])).

tff(c_221,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_218])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_224,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_221,c_8])).

tff(c_227,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_224])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_227])).

tff(c_231,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_35,B_36] :
      ( m1_pre_topc(k1_pre_topc(A_35,B_36),A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_78,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,
    ( v1_xboole_0('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_70,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_34,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_88,plain,(
    ! [B_38,A_39] :
      ( v1_tdlat_3(B_38)
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39)
      | ~ v1_tdlat_3(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_91,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_88])).

tff(c_94,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_91])).

tff(c_95,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_94])).

tff(c_169,plain,(
    ! [B_52,A_53] :
      ( v2_tex_2(u1_struct_0(B_52),A_53)
      | ~ v1_tdlat_3(B_52)
      | ~ m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_52,A_53)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_178,plain,(
    ! [A_53] :
      ( v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),A_53)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_53)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_169])).

tff(c_183,plain,(
    ! [A_53] :
      ( v2_tex_2('#skF_2',A_53)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_53)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_56,c_178])).

tff(c_188,plain,(
    ! [A_54] :
      ( v2_tex_2('#skF_2',A_54)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_54)
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_183])).

tff(c_197,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_188])).

tff(c_203,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_78,c_197])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_28,c_203])).

tff(c_206,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_208,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_242,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_208])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_242])).

tff(c_247,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_315,plain,(
    ! [B_71,A_72] :
      ( v2_tex_2(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ v1_xboole_0(B_71)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_324,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_315])).

tff(c_329,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_247,c_324])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_28,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:31:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.37  %$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.57/1.37  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.37  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.57/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.37  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.57/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.57/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.37  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 2.57/1.37  
% 2.57/1.39  tff(f_130, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 2.57/1.39  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.57/1.39  tff(f_33, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.57/1.39  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.57/1.39  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.57/1.39  tff(f_50, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 2.57/1.39  tff(f_81, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 2.57/1.39  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.57/1.39  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.57/1.39  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.57/1.39  tff(c_28, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.57/1.39  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.57/1.39  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.57/1.39  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.57/1.39  tff(c_50, plain, (![A_33, B_34]: (u1_struct_0(k1_pre_topc(A_33, B_34))=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.39  tff(c_53, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_50])).
% 2.57/1.39  tff(c_56, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_53])).
% 2.57/1.39  tff(c_4, plain, (![A_1, B_2]: (v1_pre_topc(k1_pre_topc(A_1, B_2)) | ~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_63, plain, (![B_2]: (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), B_2)) | ~m1_subset_1(B_2, k1_zfmisc_1('#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 2.57/1.39  tff(c_209, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_63])).
% 2.57/1.39  tff(c_214, plain, (![A_55, B_56]: (m1_pre_topc(k1_pre_topc(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_218, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_214])).
% 2.57/1.39  tff(c_221, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_218])).
% 2.57/1.39  tff(c_8, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.39  tff(c_224, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_221, c_8])).
% 2.57/1.39  tff(c_227, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_224])).
% 2.57/1.39  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_227])).
% 2.57/1.39  tff(c_231, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_63])).
% 2.57/1.39  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.39  tff(c_71, plain, (![A_35, B_36]: (m1_pre_topc(k1_pre_topc(A_35, B_36), A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_75, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.57/1.39  tff(c_78, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75])).
% 2.57/1.39  tff(c_10, plain, (![A_7]: (v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.57/1.39  tff(c_66, plain, (v1_xboole_0('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_10])).
% 2.57/1.39  tff(c_70, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_66])).
% 2.57/1.39  tff(c_34, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.57/1.39  tff(c_88, plain, (![B_38, A_39]: (v1_tdlat_3(B_38) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39) | ~v1_tdlat_3(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.57/1.39  tff(c_91, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_88])).
% 2.57/1.39  tff(c_94, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_91])).
% 2.57/1.39  tff(c_95, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_94])).
% 2.57/1.39  tff(c_169, plain, (![B_52, A_53]: (v2_tex_2(u1_struct_0(B_52), A_53) | ~v1_tdlat_3(B_52) | ~m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_52, A_53) | v2_struct_0(B_52) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.57/1.39  tff(c_178, plain, (![A_53]: (v2_tex_2(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), A_53) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_53) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_56, c_169])).
% 2.57/1.39  tff(c_183, plain, (![A_53]: (v2_tex_2('#skF_2', A_53) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_53) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc(A_53) | v2_struct_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_56, c_178])).
% 2.57/1.39  tff(c_188, plain, (![A_54]: (v2_tex_2('#skF_2', A_54) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_54) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(negUnitSimplification, [status(thm)], [c_70, c_183])).
% 2.57/1.39  tff(c_197, plain, (v2_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_188])).
% 2.57/1.39  tff(c_203, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_78, c_197])).
% 2.57/1.39  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_28, c_203])).
% 2.57/1.39  tff(c_206, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 2.57/1.39  tff(c_208, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_206])).
% 2.57/1.39  tff(c_242, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_208])).
% 2.57/1.39  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_242])).
% 2.57/1.39  tff(c_247, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_206])).
% 2.57/1.39  tff(c_315, plain, (![B_71, A_72]: (v2_tex_2(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~v1_xboole_0(B_71) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.57/1.39  tff(c_324, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_315])).
% 2.57/1.39  tff(c_329, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_247, c_324])).
% 2.57/1.39  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_28, c_329])).
% 2.57/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  Inference rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Ref     : 0
% 2.57/1.39  #Sup     : 53
% 2.57/1.39  #Fact    : 0
% 2.57/1.39  #Define  : 0
% 2.57/1.39  #Split   : 5
% 2.57/1.39  #Chain   : 0
% 2.57/1.39  #Close   : 0
% 2.57/1.39  
% 2.57/1.39  Ordering : KBO
% 2.57/1.39  
% 2.57/1.39  Simplification rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Subsume      : 3
% 2.57/1.39  #Demod        : 43
% 2.57/1.39  #Tautology    : 8
% 2.57/1.39  #SimpNegUnit  : 12
% 2.57/1.39  #BackRed      : 0
% 2.57/1.39  
% 2.57/1.39  #Partial instantiations: 0
% 2.57/1.39  #Strategies tried      : 1
% 2.57/1.39  
% 2.57/1.39  Timing (in seconds)
% 2.57/1.39  ----------------------
% 2.57/1.39  Preprocessing        : 0.32
% 2.57/1.39  Parsing              : 0.18
% 2.57/1.39  CNF conversion       : 0.02
% 2.57/1.39  Main loop            : 0.26
% 2.57/1.39  Inferencing          : 0.10
% 2.57/1.39  Reduction            : 0.07
% 2.57/1.39  Demodulation         : 0.05
% 2.57/1.39  BG Simplification    : 0.01
% 2.57/1.39  Subsumption          : 0.06
% 2.57/1.39  Abstraction          : 0.01
% 2.57/1.39  MUC search           : 0.00
% 2.57/1.39  Cooper               : 0.00
% 2.57/1.39  Total                : 0.61
% 2.57/1.39  Index Insertion      : 0.00
% 2.57/1.39  Index Deletion       : 0.00
% 2.57/1.39  Index Matching       : 0.00
% 2.57/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
