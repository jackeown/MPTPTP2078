%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 18.58s
% Output     : CNFRefutation 18.58s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 130 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   21
%              Number of atoms          :  188 ( 339 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_61,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_61])).

tff(c_18,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_1'(A_55),A_55)
      | A_55 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_55] :
      ( m1_subset_1('#skF_1'(A_55),A_55)
      | A_55 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_91,c_14])).

tff(c_46,plain,(
    ! [A_43,B_45] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_43),B_45),A_43)
      | ~ m1_subset_1(B_45,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k6_domain_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_4] : m1_subset_1('#skF_5',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_2] : r1_tarski('#skF_5',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_582,plain,(
    ! [C_129,B_130,A_131] :
      ( C_129 = B_130
      | ~ r1_tarski(B_130,C_129)
      | ~ v2_tex_2(C_129,A_131)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_584,plain,(
    ! [A_2,A_131] :
      ( A_2 = '#skF_5'
      | ~ v2_tex_2(A_2,A_131)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2('#skF_5',A_131)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_72,c_582])).

tff(c_893,plain,(
    ! [A_144,A_145] :
      ( A_144 = '#skF_5'
      | ~ v2_tex_2(A_144,A_145)
      | ~ m1_subset_1(A_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v3_tex_2('#skF_5',A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_584])).

tff(c_6469,plain,(
    ! [A_289,B_290] :
      ( k6_domain_1(u1_struct_0(A_289),B_290) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_289),B_290),A_289)
      | ~ v3_tex_2('#skF_5',A_289)
      | ~ l1_pre_topc(A_289)
      | ~ m1_subset_1(B_290,u1_struct_0(A_289))
      | v1_xboole_0(u1_struct_0(A_289)) ) ),
    inference(resolution,[status(thm)],[c_30,c_893])).

tff(c_6489,plain,(
    ! [A_291,B_292] :
      ( k6_domain_1(u1_struct_0(A_291),B_292) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_291)
      | v1_xboole_0(u1_struct_0(A_291))
      | ~ m1_subset_1(B_292,u1_struct_0(A_291))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_46,c_6469])).

tff(c_6651,plain,(
    ! [A_297] :
      ( k6_domain_1(u1_struct_0(A_297),'#skF_1'(u1_struct_0(A_297))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_297)
      | v1_xboole_0(u1_struct_0(A_297))
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297)
      | u1_struct_0(A_297) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_95,c_6489])).

tff(c_109,plain,(
    ! [A_60,B_61] :
      ( k6_domain_1(A_60,B_61) = k1_tarski(B_61)
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_116,plain,(
    ! [A_55] :
      ( k6_domain_1(A_55,'#skF_1'(A_55)) = k1_tarski('#skF_1'(A_55))
      | v1_xboole_0(A_55)
      | A_55 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_95,c_109])).

tff(c_19423,plain,(
    ! [A_498] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_498))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_498))
      | u1_struct_0(A_498) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_498)
      | v1_xboole_0(u1_struct_0(A_498))
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498)
      | u1_struct_0(A_498) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6651,c_116])).

tff(c_8,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_tarski(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19610,plain,(
    ! [A_498] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0(u1_struct_0(A_498))
      | u1_struct_0(A_498) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_498)
      | v1_xboole_0(u1_struct_0(A_498))
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498)
      | u1_struct_0(A_498) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19423,c_8])).

tff(c_19625,plain,(
    ! [A_499] :
      ( ~ v3_tex_2('#skF_5',A_499)
      | v1_xboole_0(u1_struct_0(A_499))
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499)
      | u1_struct_0(A_499) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_19610])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4])).

tff(c_19638,plain,(
    ! [A_500] :
      ( ~ v3_tex_2('#skF_5',A_500)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500)
      | u1_struct_0(A_500) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_19625,c_71])).

tff(c_19644,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_19638])).

tff(c_19648,plain,
    ( v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_19644])).

tff(c_19649,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_19648])).

tff(c_231,plain,(
    ! [A_91] :
      ( m1_subset_1('#skF_2'(A_91),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_242,plain,(
    ! [A_91] :
      ( v1_xboole_0('#skF_2'(A_91))
      | ~ v1_xboole_0(u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_231,c_12])).

tff(c_19772,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19649,c_242])).

tff(c_19883,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_19772])).

tff(c_19884,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_19883])).

tff(c_26,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0('#skF_2'(A_27))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19893,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_19884,c_26])).

tff(c_19899,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_19893])).

tff(c_19901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_19899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.58/8.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.58/8.80  
% 18.58/8.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.58/8.80  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 18.58/8.80  
% 18.58/8.80  %Foreground sorts:
% 18.58/8.80  
% 18.58/8.80  
% 18.58/8.80  %Background operators:
% 18.58/8.80  
% 18.58/8.80  
% 18.58/8.80  %Foreground operators:
% 18.58/8.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 18.58/8.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 18.58/8.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.58/8.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.58/8.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.58/8.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 18.58/8.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.58/8.80  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 18.58/8.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.58/8.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.58/8.80  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 18.58/8.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.58/8.80  tff('#skF_5', type, '#skF_5': $i).
% 18.58/8.80  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 18.58/8.80  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 18.58/8.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.58/8.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 18.58/8.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.58/8.80  tff('#skF_4', type, '#skF_4': $i).
% 18.58/8.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.58/8.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 18.58/8.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.58/8.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.58/8.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.58/8.80  
% 18.58/8.82  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 18.58/8.82  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 18.58/8.82  tff(f_70, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 18.58/8.82  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 18.58/8.82  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 18.58/8.82  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 18.58/8.82  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 18.58/8.82  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.58/8.82  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 18.58/8.82  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 18.58/8.82  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 18.58/8.82  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 18.58/8.82  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 18.58/8.82  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 18.58/8.82  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 18.58/8.82  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 18.58/8.82  tff(c_52, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 18.58/8.82  tff(c_48, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 18.58/8.82  tff(c_61, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 18.58/8.82  tff(c_70, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_52, c_61])).
% 18.58/8.82  tff(c_18, plain, (![A_13]: (r2_hidden('#skF_1'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.58/8.82  tff(c_91, plain, (![A_55]: (r2_hidden('#skF_1'(A_55), A_55) | A_55='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18])).
% 18.58/8.82  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.58/8.82  tff(c_95, plain, (![A_55]: (m1_subset_1('#skF_1'(A_55), A_55) | A_55='#skF_5')), inference(resolution, [status(thm)], [c_91, c_14])).
% 18.58/8.82  tff(c_46, plain, (![A_43, B_45]: (v2_tex_2(k6_domain_1(u1_struct_0(A_43), B_45), A_43) | ~m1_subset_1(B_45, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.58/8.82  tff(c_30, plain, (![A_29, B_30]: (m1_subset_1(k6_domain_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 18.58/8.82  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.58/8.82  tff(c_80, plain, (![A_4]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10])).
% 18.58/8.82  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.58/8.82  tff(c_72, plain, (![A_2]: (r1_tarski('#skF_5', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6])).
% 18.58/8.82  tff(c_582, plain, (![C_129, B_130, A_131]: (C_129=B_130 | ~r1_tarski(B_130, C_129) | ~v2_tex_2(C_129, A_131) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.58/8.82  tff(c_584, plain, (![A_2, A_131]: (A_2='#skF_5' | ~v2_tex_2(A_2, A_131) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2('#skF_5', A_131) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_72, c_582])).
% 18.58/8.82  tff(c_893, plain, (![A_144, A_145]: (A_144='#skF_5' | ~v2_tex_2(A_144, A_145) | ~m1_subset_1(A_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~v3_tex_2('#skF_5', A_145) | ~l1_pre_topc(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_584])).
% 18.58/8.82  tff(c_6469, plain, (![A_289, B_290]: (k6_domain_1(u1_struct_0(A_289), B_290)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_289), B_290), A_289) | ~v3_tex_2('#skF_5', A_289) | ~l1_pre_topc(A_289) | ~m1_subset_1(B_290, u1_struct_0(A_289)) | v1_xboole_0(u1_struct_0(A_289)))), inference(resolution, [status(thm)], [c_30, c_893])).
% 18.58/8.82  tff(c_6489, plain, (![A_291, B_292]: (k6_domain_1(u1_struct_0(A_291), B_292)='#skF_5' | ~v3_tex_2('#skF_5', A_291) | v1_xboole_0(u1_struct_0(A_291)) | ~m1_subset_1(B_292, u1_struct_0(A_291)) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_46, c_6469])).
% 18.58/8.82  tff(c_6651, plain, (![A_297]: (k6_domain_1(u1_struct_0(A_297), '#skF_1'(u1_struct_0(A_297)))='#skF_5' | ~v3_tex_2('#skF_5', A_297) | v1_xboole_0(u1_struct_0(A_297)) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297) | u1_struct_0(A_297)='#skF_5')), inference(resolution, [status(thm)], [c_95, c_6489])).
% 18.58/8.82  tff(c_109, plain, (![A_60, B_61]: (k6_domain_1(A_60, B_61)=k1_tarski(B_61) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.58/8.82  tff(c_116, plain, (![A_55]: (k6_domain_1(A_55, '#skF_1'(A_55))=k1_tarski('#skF_1'(A_55)) | v1_xboole_0(A_55) | A_55='#skF_5')), inference(resolution, [status(thm)], [c_95, c_109])).
% 18.58/8.82  tff(c_19423, plain, (![A_498]: (k1_tarski('#skF_1'(u1_struct_0(A_498)))='#skF_5' | v1_xboole_0(u1_struct_0(A_498)) | u1_struct_0(A_498)='#skF_5' | ~v3_tex_2('#skF_5', A_498) | v1_xboole_0(u1_struct_0(A_498)) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498) | u1_struct_0(A_498)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6651, c_116])).
% 18.58/8.82  tff(c_8, plain, (![A_3]: (~v1_xboole_0(k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.58/8.82  tff(c_19610, plain, (![A_498]: (~v1_xboole_0('#skF_5') | v1_xboole_0(u1_struct_0(A_498)) | u1_struct_0(A_498)='#skF_5' | ~v3_tex_2('#skF_5', A_498) | v1_xboole_0(u1_struct_0(A_498)) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498) | u1_struct_0(A_498)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_19423, c_8])).
% 18.58/8.82  tff(c_19625, plain, (![A_499]: (~v3_tex_2('#skF_5', A_499) | v1_xboole_0(u1_struct_0(A_499)) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499) | u1_struct_0(A_499)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_19610])).
% 18.58/8.82  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 18.58/8.82  tff(c_71, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4])).
% 18.58/8.82  tff(c_19638, plain, (![A_500]: (~v3_tex_2('#skF_5', A_500) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500) | u1_struct_0(A_500)='#skF_5')), inference(resolution, [status(thm)], [c_19625, c_71])).
% 18.58/8.82  tff(c_19644, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_48, c_19638])).
% 18.58/8.82  tff(c_19648, plain, (v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_19644])).
% 18.58/8.82  tff(c_19649, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_58, c_19648])).
% 18.58/8.82  tff(c_231, plain, (![A_91]: (m1_subset_1('#skF_2'(A_91), k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.58/8.82  tff(c_12, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.58/8.82  tff(c_242, plain, (![A_91]: (v1_xboole_0('#skF_2'(A_91)) | ~v1_xboole_0(u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_231, c_12])).
% 18.58/8.82  tff(c_19772, plain, (v1_xboole_0('#skF_2'('#skF_4')) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19649, c_242])).
% 18.58/8.82  tff(c_19883, plain, (v1_xboole_0('#skF_2'('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_19772])).
% 18.58/8.82  tff(c_19884, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_19883])).
% 18.58/8.82  tff(c_26, plain, (![A_27]: (~v1_xboole_0('#skF_2'(A_27)) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.58/8.82  tff(c_19893, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_19884, c_26])).
% 18.58/8.82  tff(c_19899, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_19893])).
% 18.58/8.82  tff(c_19901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_19899])).
% 18.58/8.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.58/8.82  
% 18.58/8.82  Inference rules
% 18.58/8.82  ----------------------
% 18.58/8.82  #Ref     : 0
% 18.58/8.82  #Sup     : 4627
% 18.58/8.82  #Fact    : 0
% 18.58/8.82  #Define  : 0
% 18.58/8.82  #Split   : 11
% 18.58/8.82  #Chain   : 0
% 18.58/8.82  #Close   : 0
% 18.58/8.82  
% 18.58/8.82  Ordering : KBO
% 18.58/8.82  
% 18.58/8.82  Simplification rules
% 18.58/8.82  ----------------------
% 18.58/8.82  #Subsume      : 1111
% 18.58/8.82  #Demod        : 7091
% 18.58/8.82  #Tautology    : 1893
% 18.58/8.82  #SimpNegUnit  : 1303
% 18.58/8.82  #BackRed      : 24
% 18.58/8.82  
% 18.58/8.82  #Partial instantiations: 0
% 18.58/8.82  #Strategies tried      : 1
% 18.58/8.82  
% 18.58/8.82  Timing (in seconds)
% 18.58/8.82  ----------------------
% 18.58/8.82  Preprocessing        : 0.52
% 18.58/8.82  Parsing              : 0.26
% 18.58/8.82  CNF conversion       : 0.04
% 18.58/8.82  Main loop            : 7.41
% 18.58/8.82  Inferencing          : 1.53
% 18.58/8.82  Reduction            : 2.20
% 18.58/8.82  Demodulation         : 1.52
% 18.58/8.82  BG Simplification    : 0.20
% 18.58/8.82  Subsumption          : 3.14
% 18.58/8.82  Abstraction          : 0.28
% 18.58/8.82  MUC search           : 0.00
% 18.58/8.82  Cooper               : 0.00
% 18.58/8.82  Total                : 7.97
% 18.58/8.82  Index Insertion      : 0.00
% 18.58/8.82  Index Deletion       : 0.00
% 18.58/8.82  Index Matching       : 0.00
% 18.58/8.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
