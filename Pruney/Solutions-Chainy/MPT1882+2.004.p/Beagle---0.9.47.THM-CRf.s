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
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 260 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 996 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_47,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_110,plain,(
    ! [A_39,B_40] :
      ( '#skF_1'(A_39,B_40) != B_40
      | v3_tex_2(B_40,A_39)
      | ~ v2_tex_2(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_121,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_117])).

tff(c_122,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_121])).

tff(c_123,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46])).

tff(c_183,plain,(
    ! [B_55,A_56] :
      ( v2_tex_2(B_55,A_56)
      | ~ v1_zfmisc_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | v1_xboole_0(B_55)
      | ~ l1_pre_topc(A_56)
      | ~ v2_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_190,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_183])).

tff(c_194,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_48,c_190])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_123,c_194])).

tff(c_198,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_207,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,'#skF_1'(A_60,B_59))
      | v3_tex_2(B_59,A_60)
      | ~ v2_tex_2(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_212,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_207])).

tff(c_216,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_198,c_212])).

tff(c_217,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_216])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [B_29,A_30] :
      ( v1_xboole_0(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_4,B_5] :
      ( v1_xboole_0(A_4)
      | ~ v1_xboole_0(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_220,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_217,c_73])).

tff(c_226,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_220])).

tff(c_197,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_22,plain,(
    ! [B_19,A_17] :
      ( B_19 = A_17
      | ~ r1_tarski(A_17,B_19)
      | ~ v1_zfmisc_1(B_19)
      | v1_xboole_0(B_19)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_223,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_217,c_22])).

tff(c_229,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_197,c_223])).

tff(c_230,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_229])).

tff(c_231,plain,(
    ! [A_61,B_62] :
      ( v2_tex_2('#skF_1'(A_61,B_62),A_61)
      | v3_tex_2(B_62,A_61)
      | ~ v2_tex_2(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_231])).

tff(c_240,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_198,c_236])).

tff(c_241,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_240])).

tff(c_16,plain,(
    ! [A_7,B_13] :
      ( m1_subset_1('#skF_1'(A_7,B_13),k1_zfmisc_1(u1_struct_0(A_7)))
      | v3_tex_2(B_13,A_7)
      | ~ v2_tex_2(B_13,A_7)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_322,plain,(
    ! [B_75,A_76] :
      ( v1_zfmisc_1(B_75)
      | ~ v2_tex_2(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(B_75)
      | ~ l1_pre_topc(A_76)
      | ~ v2_tdlat_3(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_479,plain,(
    ! [A_102,B_103] :
      ( v1_zfmisc_1('#skF_1'(A_102,B_103))
      | ~ v2_tex_2('#skF_1'(A_102,B_103),A_102)
      | v1_xboole_0('#skF_1'(A_102,B_103))
      | ~ v2_tdlat_3(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102)
      | v3_tex_2(B_103,A_102)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_16,c_322])).

tff(c_485,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_241,c_479])).

tff(c_490,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_198,c_36,c_34,c_485])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_38,c_226,c_230,c_490])).

tff(c_493,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_495,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_46])).

tff(c_539,plain,(
    ! [B_115,A_116] :
      ( v2_tex_2(B_115,A_116)
      | ~ v3_tex_2(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_546,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_539])).

tff(c_550,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_495,c_546])).

tff(c_676,plain,(
    ! [B_139,A_140] :
      ( v1_zfmisc_1(B_139)
      | ~ v2_tex_2(B_139,A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | v1_xboole_0(B_139)
      | ~ l1_pre_topc(A_140)
      | ~ v2_tdlat_3(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_686,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_676])).

tff(c_691,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_550,c_686])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_493,c_691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/2.05  
% 3.74/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/2.05  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.74/2.05  
% 3.74/2.05  %Foreground sorts:
% 3.74/2.05  
% 3.74/2.05  
% 3.74/2.05  %Background operators:
% 3.74/2.05  
% 3.74/2.05  
% 3.74/2.05  %Foreground operators:
% 3.74/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.74/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.74/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/2.05  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.74/2.05  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.74/2.05  tff('#skF_2', type, '#skF_2': $i).
% 3.74/2.05  tff('#skF_3', type, '#skF_3': $i).
% 3.74/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/2.05  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.74/2.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.74/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/2.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.74/2.05  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.74/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/2.05  
% 4.08/2.08  tff(f_112, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 4.08/2.08  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.08/2.08  tff(f_92, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 4.08/2.08  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.08/2.08  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.08/2.08  tff(f_73, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 4.08/2.08  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_30, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_40, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_47, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.08/2.08  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_110, plain, (![A_39, B_40]: ('#skF_1'(A_39, B_40)!=B_40 | v3_tex_2(B_40, A_39) | ~v2_tex_2(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/2.08  tff(c_117, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_110])).
% 4.08/2.08  tff(c_121, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_117])).
% 4.08/2.08  tff(c_122, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47, c_121])).
% 4.08/2.08  tff(c_123, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_122])).
% 4.08/2.08  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_34, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_46, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.08/2.08  tff(c_48, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_47, c_46])).
% 4.08/2.08  tff(c_183, plain, (![B_55, A_56]: (v2_tex_2(B_55, A_56) | ~v1_zfmisc_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | v1_xboole_0(B_55) | ~l1_pre_topc(A_56) | ~v2_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.08/2.08  tff(c_190, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_183])).
% 4.08/2.08  tff(c_194, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_48, c_190])).
% 4.08/2.08  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_123, c_194])).
% 4.08/2.08  tff(c_198, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_122])).
% 4.08/2.08  tff(c_207, plain, (![B_59, A_60]: (r1_tarski(B_59, '#skF_1'(A_60, B_59)) | v3_tex_2(B_59, A_60) | ~v2_tex_2(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/2.08  tff(c_212, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_207])).
% 4.08/2.08  tff(c_216, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_198, c_212])).
% 4.08/2.08  tff(c_217, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_47, c_216])).
% 4.08/2.08  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.08/2.08  tff(c_66, plain, (![B_29, A_30]: (v1_xboole_0(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.08/2.08  tff(c_73, plain, (![A_4, B_5]: (v1_xboole_0(A_4) | ~v1_xboole_0(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_66])).
% 4.08/2.08  tff(c_220, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_217, c_73])).
% 4.08/2.08  tff(c_226, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_220])).
% 4.08/2.08  tff(c_197, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_122])).
% 4.08/2.08  tff(c_22, plain, (![B_19, A_17]: (B_19=A_17 | ~r1_tarski(A_17, B_19) | ~v1_zfmisc_1(B_19) | v1_xboole_0(B_19) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/2.08  tff(c_223, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_217, c_22])).
% 4.08/2.08  tff(c_229, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_197, c_223])).
% 4.08/2.08  tff(c_230, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_226, c_229])).
% 4.08/2.08  tff(c_231, plain, (![A_61, B_62]: (v2_tex_2('#skF_1'(A_61, B_62), A_61) | v3_tex_2(B_62, A_61) | ~v2_tex_2(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/2.08  tff(c_236, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_231])).
% 4.08/2.08  tff(c_240, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_198, c_236])).
% 4.08/2.08  tff(c_241, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47, c_240])).
% 4.08/2.08  tff(c_16, plain, (![A_7, B_13]: (m1_subset_1('#skF_1'(A_7, B_13), k1_zfmisc_1(u1_struct_0(A_7))) | v3_tex_2(B_13, A_7) | ~v2_tex_2(B_13, A_7) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/2.08  tff(c_322, plain, (![B_75, A_76]: (v1_zfmisc_1(B_75) | ~v2_tex_2(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(B_75) | ~l1_pre_topc(A_76) | ~v2_tdlat_3(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.08/2.08  tff(c_479, plain, (![A_102, B_103]: (v1_zfmisc_1('#skF_1'(A_102, B_103)) | ~v2_tex_2('#skF_1'(A_102, B_103), A_102) | v1_xboole_0('#skF_1'(A_102, B_103)) | ~v2_tdlat_3(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102) | v3_tex_2(B_103, A_102) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_16, c_322])).
% 4.08/2.08  tff(c_485, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_241, c_479])).
% 4.08/2.08  tff(c_490, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_198, c_36, c_34, c_485])).
% 4.08/2.08  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_38, c_226, c_230, c_490])).
% 4.08/2.08  tff(c_493, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.08/2.08  tff(c_495, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_493, c_46])).
% 4.08/2.08  tff(c_539, plain, (![B_115, A_116]: (v2_tex_2(B_115, A_116) | ~v3_tex_2(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/2.08  tff(c_546, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_539])).
% 4.08/2.08  tff(c_550, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_495, c_546])).
% 4.08/2.08  tff(c_676, plain, (![B_139, A_140]: (v1_zfmisc_1(B_139) | ~v2_tex_2(B_139, A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | v1_xboole_0(B_139) | ~l1_pre_topc(A_140) | ~v2_tdlat_3(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.08/2.08  tff(c_686, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_676])).
% 4.08/2.08  tff(c_691, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_550, c_686])).
% 4.08/2.08  tff(c_693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_493, c_691])).
% 4.08/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/2.08  
% 4.08/2.08  Inference rules
% 4.08/2.08  ----------------------
% 4.08/2.08  #Ref     : 0
% 4.08/2.08  #Sup     : 115
% 4.08/2.08  #Fact    : 0
% 4.08/2.08  #Define  : 0
% 4.08/2.08  #Split   : 6
% 4.08/2.08  #Chain   : 0
% 4.08/2.08  #Close   : 0
% 4.08/2.08  
% 4.08/2.08  Ordering : KBO
% 4.08/2.08  
% 4.08/2.08  Simplification rules
% 4.08/2.08  ----------------------
% 4.08/2.08  #Subsume      : 29
% 4.08/2.08  #Demod        : 109
% 4.08/2.08  #Tautology    : 18
% 4.08/2.08  #SimpNegUnit  : 39
% 4.08/2.08  #BackRed      : 0
% 4.08/2.08  
% 4.08/2.08  #Partial instantiations: 0
% 4.08/2.08  #Strategies tried      : 1
% 4.08/2.08  
% 4.08/2.08  Timing (in seconds)
% 4.08/2.08  ----------------------
% 4.08/2.09  Preprocessing        : 0.48
% 4.08/2.09  Parsing              : 0.26
% 4.08/2.09  CNF conversion       : 0.04
% 4.08/2.09  Main loop            : 0.65
% 4.08/2.09  Inferencing          : 0.25
% 4.08/2.09  Reduction            : 0.17
% 4.08/2.09  Demodulation         : 0.10
% 4.08/2.09  BG Simplification    : 0.04
% 4.08/2.09  Subsumption          : 0.15
% 4.08/2.09  Abstraction          : 0.03
% 4.08/2.09  MUC search           : 0.00
% 4.08/2.09  Cooper               : 0.00
% 4.08/2.09  Total                : 1.20
% 4.08/2.09  Index Insertion      : 0.00
% 4.08/2.09  Index Deletion       : 0.00
% 4.08/2.09  Index Matching       : 0.00
% 4.08/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
