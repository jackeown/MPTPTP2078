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
% DateTime   : Thu Dec  3 10:26:42 EST 2020

% Result     : Theorem 31.57s
% Output     : CNFRefutation 31.57s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 389 expanded)
%              Number of leaves         :   34 ( 153 expanded)
%              Depth                    :   19
%              Number of atoms          :  343 (1830 expanded)
%              Number of equality atoms :   21 (  91 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,C)
                        & m1_pre_topc(D,C) )
                     => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_84,plain,(
    ! [B_85,A_86] :
      ( l1_pre_topc(B_85)
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_110,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_99])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_315,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_pre_topc(k1_tsep_1(A_114,B_115,C_116),A_114)
      | ~ m1_pre_topc(C_116,A_114)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_115,A_114)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    ! [B_45,A_43] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_322,plain,(
    ! [A_114,B_115,C_116] :
      ( l1_pre_topc(k1_tsep_1(A_114,B_115,C_116))
      | ~ m1_pre_topc(C_116,A_114)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_115,A_114)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_315,c_34])).

tff(c_40,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_pre_topc(k1_tsep_1(A_61,B_62,C_63),A_61)
      | ~ m1_pre_topc(C_63,A_61)
      | v2_struct_0(C_63)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_22,plain,(
    ! [B_24,A_2] :
      ( r1_tarski(k2_struct_0(B_24),k2_struct_0(A_2))
      | ~ m1_pre_topc(B_24,A_2)
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_502,plain,(
    ! [A_137,B_138,C_139] :
      ( l1_pre_topc(k1_tsep_1(A_137,B_138,C_139))
      | ~ m1_pre_topc(C_139,A_137)
      | v2_struct_0(C_139)
      | ~ m1_pre_topc(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_315,c_34])).

tff(c_32,plain,(
    ! [A_42] :
      ( l1_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    ! [A_83] :
      ( u1_struct_0(A_83) = k2_struct_0(A_83)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_506,plain,(
    ! [A_137,B_138,C_139] :
      ( u1_struct_0(k1_tsep_1(A_137,B_138,C_139)) = k2_struct_0(k1_tsep_1(A_137,B_138,C_139))
      | ~ m1_pre_topc(C_139,A_137)
      | v2_struct_0(C_139)
      | ~ m1_pre_topc(B_138,A_137)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_502,c_78])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_105,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_90])).

tff(c_118,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_78])).

tff(c_56,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_84])).

tff(c_102,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_87])).

tff(c_114,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_78])).

tff(c_42,plain,(
    ! [A_61,B_62,C_63] :
      ( v1_pre_topc(k1_tsep_1(A_61,B_62,C_63))
      | ~ m1_pre_topc(C_63,A_61)
      | v2_struct_0(C_63)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1307,plain,(
    ! [A_270,B_271,C_272] :
      ( u1_struct_0(k1_tsep_1(A_270,B_271,C_272)) = k2_xboole_0(u1_struct_0(B_271),u1_struct_0(C_272))
      | ~ m1_pre_topc(k1_tsep_1(A_270,B_271,C_272),A_270)
      | ~ v1_pre_topc(k1_tsep_1(A_270,B_271,C_272))
      | v2_struct_0(k1_tsep_1(A_270,B_271,C_272))
      | ~ m1_pre_topc(C_272,A_270)
      | v2_struct_0(C_272)
      | ~ m1_pre_topc(B_271,A_270)
      | v2_struct_0(B_271)
      | ~ l1_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1335,plain,(
    ! [A_283,B_284,C_285] :
      ( u1_struct_0(k1_tsep_1(A_283,B_284,C_285)) = k2_xboole_0(u1_struct_0(B_284),u1_struct_0(C_285))
      | ~ v1_pre_topc(k1_tsep_1(A_283,B_284,C_285))
      | v2_struct_0(k1_tsep_1(A_283,B_284,C_285))
      | ~ m1_pre_topc(C_285,A_283)
      | v2_struct_0(C_285)
      | ~ m1_pre_topc(B_284,A_283)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_40,c_1307])).

tff(c_44,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ v2_struct_0(k1_tsep_1(A_61,B_62,C_63))
      | ~ m1_pre_topc(C_63,A_61)
      | v2_struct_0(C_63)
      | ~ m1_pre_topc(B_62,A_61)
      | v2_struct_0(B_62)
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1578,plain,(
    ! [A_286,B_287,C_288] :
      ( u1_struct_0(k1_tsep_1(A_286,B_287,C_288)) = k2_xboole_0(u1_struct_0(B_287),u1_struct_0(C_288))
      | ~ v1_pre_topc(k1_tsep_1(A_286,B_287,C_288))
      | ~ m1_pre_topc(C_288,A_286)
      | v2_struct_0(C_288)
      | ~ m1_pre_topc(B_287,A_286)
      | v2_struct_0(B_287)
      | ~ l1_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_1335,c_44])).

tff(c_1582,plain,(
    ! [A_289,B_290,C_291] :
      ( u1_struct_0(k1_tsep_1(A_289,B_290,C_291)) = k2_xboole_0(u1_struct_0(B_290),u1_struct_0(C_291))
      | ~ m1_pre_topc(C_291,A_289)
      | v2_struct_0(C_291)
      | ~ m1_pre_topc(B_290,A_289)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(resolution,[status(thm)],[c_42,c_1578])).

tff(c_1798,plain,(
    ! [A_289,B_290] :
      ( u1_struct_0(k1_tsep_1(A_289,B_290,'#skF_7')) = k2_xboole_0(u1_struct_0(B_290),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_289)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_290,A_289)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_1582])).

tff(c_4989,plain,(
    ! [A_314,B_315] :
      ( u1_struct_0(k1_tsep_1(A_314,B_315,'#skF_7')) = k2_xboole_0(u1_struct_0(B_315),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_314)
      | ~ m1_pre_topc(B_315,A_314)
      | v2_struct_0(B_315)
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1798])).

tff(c_5293,plain,(
    ! [A_314] :
      ( u1_struct_0(k1_tsep_1(A_314,'#skF_5','#skF_7')) = k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_314)
      | ~ m1_pre_topc('#skF_5',A_314)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_4989])).

tff(c_5562,plain,(
    ! [A_317] :
      ( u1_struct_0(k1_tsep_1(A_317,'#skF_5','#skF_7')) = k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_317)
      | ~ m1_pre_topc('#skF_5',A_317)
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5293])).

tff(c_5778,plain,(
    ! [A_137] :
      ( k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')) = k2_struct_0(k1_tsep_1(A_137,'#skF_5','#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_137)
      | ~ m1_pre_topc('#skF_5',A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ m1_pre_topc('#skF_7',A_137)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc('#skF_5',A_137)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_5562])).

tff(c_5796,plain,(
    ! [A_137] :
      ( k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')) = k2_struct_0(k1_tsep_1(A_137,'#skF_5','#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_137)
      | ~ m1_pre_topc('#skF_5',A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ m1_pre_topc('#skF_7',A_137)
      | ~ m1_pre_topc('#skF_5',A_137)
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_5778])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_5326,plain,(
    ! [A_314] :
      ( u1_struct_0(k1_tsep_1(A_314,'#skF_5','#skF_7')) = k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_7',A_314)
      | ~ m1_pre_topc('#skF_5',A_314)
      | ~ l1_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5293])).

tff(c_122,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_78])).

tff(c_161,plain,(
    ! [B_92,C_93,A_94] :
      ( r1_tarski(u1_struct_0(B_92),u1_struct_0(C_93))
      | ~ m1_pre_topc(B_92,C_93)
      | ~ m1_pre_topc(C_93,A_94)
      | ~ m1_pre_topc(B_92,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_171,plain,(
    ! [B_92] :
      ( r1_tarski(u1_struct_0(B_92),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_92,'#skF_6')
      | ~ m1_pre_topc(B_92,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_161])).

tff(c_186,plain,(
    ! [B_92] :
      ( r1_tarski(u1_struct_0(B_92),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_92,'#skF_6')
      | ~ m1_pre_topc(B_92,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_122,c_171])).

tff(c_5749,plain,(
    ! [A_317] :
      ( r1_tarski(k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc(k1_tsep_1(A_317,'#skF_5','#skF_7'),'#skF_6')
      | ~ m1_pre_topc(k1_tsep_1(A_317,'#skF_5','#skF_7'),'#skF_4')
      | ~ m1_pre_topc('#skF_7',A_317)
      | ~ m1_pre_topc('#skF_5',A_317)
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5562,c_186])).

tff(c_44082,plain,(
    r1_tarski(k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')),k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5749])).

tff(c_44085,plain,(
    ! [A_762] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(A_762,'#skF_5','#skF_7')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_7',A_762)
      | ~ m1_pre_topc('#skF_5',A_762)
      | ~ l1_pre_topc(A_762)
      | v2_struct_0(A_762) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5326,c_44082])).

tff(c_144,plain,(
    ! [B_89,C_90,A_91] :
      ( m1_pre_topc(B_89,C_90)
      | ~ r1_tarski(u1_struct_0(B_89),u1_struct_0(C_90))
      | ~ m1_pre_topc(C_90,A_91)
      | ~ m1_pre_topc(B_89,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_156,plain,(
    ! [B_89,A_91] :
      ( m1_pre_topc(B_89,'#skF_6')
      | ~ r1_tarski(u1_struct_0(B_89),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_91)
      | ~ m1_pre_topc(B_89,A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_144])).

tff(c_44326,plain,(
    ! [A_766,A_767] :
      ( m1_pre_topc(k1_tsep_1(A_766,'#skF_5','#skF_7'),'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_767)
      | ~ m1_pre_topc(k1_tsep_1(A_766,'#skF_5','#skF_7'),A_767)
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | ~ m1_pre_topc('#skF_7',A_766)
      | ~ m1_pre_topc('#skF_5',A_766)
      | ~ l1_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_44085,c_156])).

tff(c_44329,plain,(
    ! [A_61] :
      ( m1_pre_topc(k1_tsep_1(A_61,'#skF_5','#skF_7'),'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_61)
      | ~ v2_pre_topc(A_61)
      | ~ m1_pre_topc('#skF_7',A_61)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc('#skF_5',A_61)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_40,c_44326])).

tff(c_44333,plain,(
    ! [A_768] :
      ( m1_pre_topc(k1_tsep_1(A_768,'#skF_5','#skF_7'),'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_768)
      | ~ v2_pre_topc(A_768)
      | ~ m1_pre_topc('#skF_7',A_768)
      | ~ m1_pre_topc('#skF_5',A_768)
      | ~ l1_pre_topc(A_768)
      | v2_struct_0(A_768) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_44329])).

tff(c_50,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_4','#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44343,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44333,c_50])).

tff(c_44355,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_56,c_70,c_60,c_44343])).

tff(c_44357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_44355])).

tff(c_44359,plain,(
    ~ r1_tarski(k2_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')),k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5749])).

tff(c_44418,plain,(
    ! [A_771] :
      ( ~ r1_tarski(k2_struct_0(k1_tsep_1(A_771,'#skF_5','#skF_7')),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_7',A_771)
      | ~ m1_pre_topc('#skF_5',A_771)
      | ~ l1_pre_topc(A_771)
      | v2_struct_0(A_771)
      | ~ m1_pre_topc('#skF_7',A_771)
      | ~ m1_pre_topc('#skF_5',A_771)
      | ~ l1_pre_topc(A_771)
      | v2_struct_0(A_771) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5796,c_44359])).

tff(c_44424,plain,(
    ! [A_771] :
      ( ~ m1_pre_topc('#skF_7',A_771)
      | ~ m1_pre_topc('#skF_5',A_771)
      | ~ l1_pre_topc(A_771)
      | v2_struct_0(A_771)
      | ~ m1_pre_topc(k1_tsep_1(A_771,'#skF_5','#skF_7'),'#skF_6')
      | ~ l1_pre_topc(k1_tsep_1(A_771,'#skF_5','#skF_7'))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_44418])).

tff(c_44618,plain,(
    ! [A_774] :
      ( ~ m1_pre_topc('#skF_7',A_774)
      | ~ m1_pre_topc('#skF_5',A_774)
      | ~ l1_pre_topc(A_774)
      | v2_struct_0(A_774)
      | ~ m1_pre_topc(k1_tsep_1(A_774,'#skF_5','#skF_7'),'#skF_6')
      | ~ l1_pre_topc(k1_tsep_1(A_774,'#skF_5','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_44424])).

tff(c_44622,plain,
    ( ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_5','#skF_7'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_44618])).

tff(c_44625,plain,
    ( ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_5','#skF_7'))
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_54,c_52,c_44622])).

tff(c_44626,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_6','#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_66,c_58,c_44625])).

tff(c_44629,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_322,c_44626])).

tff(c_44632,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_54,c_52,c_44629])).

tff(c_44634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_66,c_58,c_44632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.57/20.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.57/20.39  
% 31.57/20.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.57/20.39  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 31.57/20.39  
% 31.57/20.39  %Foreground sorts:
% 31.57/20.39  
% 31.57/20.39  
% 31.57/20.39  %Background operators:
% 31.57/20.39  
% 31.57/20.39  
% 31.57/20.39  %Foreground operators:
% 31.57/20.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 31.57/20.39  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 31.57/20.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 31.57/20.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 31.57/20.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.57/20.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.57/20.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 31.57/20.39  tff('#skF_7', type, '#skF_7': $i).
% 31.57/20.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 31.57/20.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.57/20.39  tff('#skF_5', type, '#skF_5': $i).
% 31.57/20.39  tff('#skF_6', type, '#skF_6': $i).
% 31.57/20.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 31.57/20.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.57/20.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 31.57/20.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.57/20.39  tff('#skF_4', type, '#skF_4': $i).
% 31.57/20.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.57/20.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 31.57/20.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 31.57/20.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 31.57/20.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 31.57/20.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 31.57/20.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 31.57/20.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 31.57/20.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.57/20.39  
% 31.57/20.41  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 31.57/20.41  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 31.57/20.41  tff(f_112, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 31.57/20.41  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 31.57/20.41  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 31.57/20.41  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 31.57/20.41  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 31.57/20.41  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 31.57/20.41  tff(c_62, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_58, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_84, plain, (![B_85, A_86]: (l1_pre_topc(B_85) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.57/20.41  tff(c_99, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_84])).
% 31.57/20.41  tff(c_110, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_99])).
% 31.57/20.41  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_52, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_315, plain, (![A_114, B_115, C_116]: (m1_pre_topc(k1_tsep_1(A_114, B_115, C_116), A_114) | ~m1_pre_topc(C_116, A_114) | v2_struct_0(C_116) | ~m1_pre_topc(B_115, A_114) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.57/20.41  tff(c_34, plain, (![B_45, A_43]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.57/20.41  tff(c_322, plain, (![A_114, B_115, C_116]: (l1_pre_topc(k1_tsep_1(A_114, B_115, C_116)) | ~m1_pre_topc(C_116, A_114) | v2_struct_0(C_116) | ~m1_pre_topc(B_115, A_114) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_315, c_34])).
% 31.57/20.41  tff(c_40, plain, (![A_61, B_62, C_63]: (m1_pre_topc(k1_tsep_1(A_61, B_62, C_63), A_61) | ~m1_pre_topc(C_63, A_61) | v2_struct_0(C_63) | ~m1_pre_topc(B_62, A_61) | v2_struct_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.57/20.41  tff(c_22, plain, (![B_24, A_2]: (r1_tarski(k2_struct_0(B_24), k2_struct_0(A_2)) | ~m1_pre_topc(B_24, A_2) | ~l1_pre_topc(B_24) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_50])).
% 31.57/20.41  tff(c_502, plain, (![A_137, B_138, C_139]: (l1_pre_topc(k1_tsep_1(A_137, B_138, C_139)) | ~m1_pre_topc(C_139, A_137) | v2_struct_0(C_139) | ~m1_pre_topc(B_138, A_137) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_315, c_34])).
% 31.57/20.41  tff(c_32, plain, (![A_42]: (l1_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 31.57/20.41  tff(c_74, plain, (![A_83]: (u1_struct_0(A_83)=k2_struct_0(A_83) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.57/20.41  tff(c_78, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_32, c_74])).
% 31.57/20.41  tff(c_506, plain, (![A_137, B_138, C_139]: (u1_struct_0(k1_tsep_1(A_137, B_138, C_139))=k2_struct_0(k1_tsep_1(A_137, B_138, C_139)) | ~m1_pre_topc(C_139, A_137) | v2_struct_0(C_139) | ~m1_pre_topc(B_138, A_137) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_502, c_78])).
% 31.57/20.41  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_90, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_84])).
% 31.57/20.41  tff(c_105, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_90])).
% 31.57/20.41  tff(c_118, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_105, c_78])).
% 31.57/20.41  tff(c_56, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_87, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_56, c_84])).
% 31.57/20.41  tff(c_102, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_87])).
% 31.57/20.41  tff(c_114, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_102, c_78])).
% 31.57/20.41  tff(c_42, plain, (![A_61, B_62, C_63]: (v1_pre_topc(k1_tsep_1(A_61, B_62, C_63)) | ~m1_pre_topc(C_63, A_61) | v2_struct_0(C_63) | ~m1_pre_topc(B_62, A_61) | v2_struct_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.57/20.41  tff(c_1307, plain, (![A_270, B_271, C_272]: (u1_struct_0(k1_tsep_1(A_270, B_271, C_272))=k2_xboole_0(u1_struct_0(B_271), u1_struct_0(C_272)) | ~m1_pre_topc(k1_tsep_1(A_270, B_271, C_272), A_270) | ~v1_pre_topc(k1_tsep_1(A_270, B_271, C_272)) | v2_struct_0(k1_tsep_1(A_270, B_271, C_272)) | ~m1_pre_topc(C_272, A_270) | v2_struct_0(C_272) | ~m1_pre_topc(B_271, A_270) | v2_struct_0(B_271) | ~l1_pre_topc(A_270) | v2_struct_0(A_270))), inference(cnfTransformation, [status(thm)], [f_90])).
% 31.57/20.41  tff(c_1335, plain, (![A_283, B_284, C_285]: (u1_struct_0(k1_tsep_1(A_283, B_284, C_285))=k2_xboole_0(u1_struct_0(B_284), u1_struct_0(C_285)) | ~v1_pre_topc(k1_tsep_1(A_283, B_284, C_285)) | v2_struct_0(k1_tsep_1(A_283, B_284, C_285)) | ~m1_pre_topc(C_285, A_283) | v2_struct_0(C_285) | ~m1_pre_topc(B_284, A_283) | v2_struct_0(B_284) | ~l1_pre_topc(A_283) | v2_struct_0(A_283))), inference(resolution, [status(thm)], [c_40, c_1307])).
% 31.57/20.41  tff(c_44, plain, (![A_61, B_62, C_63]: (~v2_struct_0(k1_tsep_1(A_61, B_62, C_63)) | ~m1_pre_topc(C_63, A_61) | v2_struct_0(C_63) | ~m1_pre_topc(B_62, A_61) | v2_struct_0(B_62) | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.57/20.41  tff(c_1578, plain, (![A_286, B_287, C_288]: (u1_struct_0(k1_tsep_1(A_286, B_287, C_288))=k2_xboole_0(u1_struct_0(B_287), u1_struct_0(C_288)) | ~v1_pre_topc(k1_tsep_1(A_286, B_287, C_288)) | ~m1_pre_topc(C_288, A_286) | v2_struct_0(C_288) | ~m1_pre_topc(B_287, A_286) | v2_struct_0(B_287) | ~l1_pre_topc(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_1335, c_44])).
% 31.57/20.41  tff(c_1582, plain, (![A_289, B_290, C_291]: (u1_struct_0(k1_tsep_1(A_289, B_290, C_291))=k2_xboole_0(u1_struct_0(B_290), u1_struct_0(C_291)) | ~m1_pre_topc(C_291, A_289) | v2_struct_0(C_291) | ~m1_pre_topc(B_290, A_289) | v2_struct_0(B_290) | ~l1_pre_topc(A_289) | v2_struct_0(A_289))), inference(resolution, [status(thm)], [c_42, c_1578])).
% 31.57/20.41  tff(c_1798, plain, (![A_289, B_290]: (u1_struct_0(k1_tsep_1(A_289, B_290, '#skF_7'))=k2_xboole_0(u1_struct_0(B_290), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_289) | v2_struct_0('#skF_7') | ~m1_pre_topc(B_290, A_289) | v2_struct_0(B_290) | ~l1_pre_topc(A_289) | v2_struct_0(A_289))), inference(superposition, [status(thm), theory('equality')], [c_114, c_1582])).
% 31.57/20.41  tff(c_4989, plain, (![A_314, B_315]: (u1_struct_0(k1_tsep_1(A_314, B_315, '#skF_7'))=k2_xboole_0(u1_struct_0(B_315), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_314) | ~m1_pre_topc(B_315, A_314) | v2_struct_0(B_315) | ~l1_pre_topc(A_314) | v2_struct_0(A_314))), inference(negUnitSimplification, [status(thm)], [c_58, c_1798])).
% 31.57/20.41  tff(c_5293, plain, (![A_314]: (u1_struct_0(k1_tsep_1(A_314, '#skF_5', '#skF_7'))=k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_314) | ~m1_pre_topc('#skF_5', A_314) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_314) | v2_struct_0(A_314))), inference(superposition, [status(thm), theory('equality')], [c_118, c_4989])).
% 31.57/20.41  tff(c_5562, plain, (![A_317]: (u1_struct_0(k1_tsep_1(A_317, '#skF_5', '#skF_7'))=k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_317) | ~m1_pre_topc('#skF_5', A_317) | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(negUnitSimplification, [status(thm)], [c_66, c_5293])).
% 31.57/20.41  tff(c_5778, plain, (![A_137]: (k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))=k2_struct_0(k1_tsep_1(A_137, '#skF_5', '#skF_7')) | ~m1_pre_topc('#skF_7', A_137) | ~m1_pre_topc('#skF_5', A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137) | ~m1_pre_topc('#skF_7', A_137) | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_5', A_137) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(superposition, [status(thm), theory('equality')], [c_506, c_5562])).
% 31.57/20.41  tff(c_5796, plain, (![A_137]: (k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))=k2_struct_0(k1_tsep_1(A_137, '#skF_5', '#skF_7')) | ~m1_pre_topc('#skF_7', A_137) | ~m1_pre_topc('#skF_5', A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137) | ~m1_pre_topc('#skF_7', A_137) | ~m1_pre_topc('#skF_5', A_137) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_5778])).
% 31.57/20.41  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_5326, plain, (![A_314]: (u1_struct_0(k1_tsep_1(A_314, '#skF_5', '#skF_7'))=k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', A_314) | ~m1_pre_topc('#skF_5', A_314) | ~l1_pre_topc(A_314) | v2_struct_0(A_314))), inference(negUnitSimplification, [status(thm)], [c_66, c_5293])).
% 31.57/20.41  tff(c_122, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_110, c_78])).
% 31.57/20.41  tff(c_161, plain, (![B_92, C_93, A_94]: (r1_tarski(u1_struct_0(B_92), u1_struct_0(C_93)) | ~m1_pre_topc(B_92, C_93) | ~m1_pre_topc(C_93, A_94) | ~m1_pre_topc(B_92, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_126])).
% 31.57/20.41  tff(c_171, plain, (![B_92]: (r1_tarski(u1_struct_0(B_92), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_92, '#skF_6') | ~m1_pre_topc(B_92, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_161])).
% 31.57/20.41  tff(c_186, plain, (![B_92]: (r1_tarski(u1_struct_0(B_92), k2_struct_0('#skF_6')) | ~m1_pre_topc(B_92, '#skF_6') | ~m1_pre_topc(B_92, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_122, c_171])).
% 31.57/20.41  tff(c_5749, plain, (![A_317]: (r1_tarski(k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')), k2_struct_0('#skF_6')) | ~m1_pre_topc(k1_tsep_1(A_317, '#skF_5', '#skF_7'), '#skF_6') | ~m1_pre_topc(k1_tsep_1(A_317, '#skF_5', '#skF_7'), '#skF_4') | ~m1_pre_topc('#skF_7', A_317) | ~m1_pre_topc('#skF_5', A_317) | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(superposition, [status(thm), theory('equality')], [c_5562, c_186])).
% 31.57/20.41  tff(c_44082, plain, (r1_tarski(k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')), k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_5749])).
% 31.57/20.41  tff(c_44085, plain, (![A_762]: (r1_tarski(u1_struct_0(k1_tsep_1(A_762, '#skF_5', '#skF_7')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', A_762) | ~m1_pre_topc('#skF_5', A_762) | ~l1_pre_topc(A_762) | v2_struct_0(A_762))), inference(superposition, [status(thm), theory('equality')], [c_5326, c_44082])).
% 31.57/20.41  tff(c_144, plain, (![B_89, C_90, A_91]: (m1_pre_topc(B_89, C_90) | ~r1_tarski(u1_struct_0(B_89), u1_struct_0(C_90)) | ~m1_pre_topc(C_90, A_91) | ~m1_pre_topc(B_89, A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_126])).
% 31.57/20.41  tff(c_156, plain, (![B_89, A_91]: (m1_pre_topc(B_89, '#skF_6') | ~r1_tarski(u1_struct_0(B_89), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', A_91) | ~m1_pre_topc(B_89, A_91) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(superposition, [status(thm), theory('equality')], [c_122, c_144])).
% 31.57/20.41  tff(c_44326, plain, (![A_766, A_767]: (m1_pre_topc(k1_tsep_1(A_766, '#skF_5', '#skF_7'), '#skF_6') | ~m1_pre_topc('#skF_6', A_767) | ~m1_pre_topc(k1_tsep_1(A_766, '#skF_5', '#skF_7'), A_767) | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | ~m1_pre_topc('#skF_7', A_766) | ~m1_pre_topc('#skF_5', A_766) | ~l1_pre_topc(A_766) | v2_struct_0(A_766))), inference(resolution, [status(thm)], [c_44085, c_156])).
% 31.57/20.41  tff(c_44329, plain, (![A_61]: (m1_pre_topc(k1_tsep_1(A_61, '#skF_5', '#skF_7'), '#skF_6') | ~m1_pre_topc('#skF_6', A_61) | ~v2_pre_topc(A_61) | ~m1_pre_topc('#skF_7', A_61) | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_5', A_61) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_40, c_44326])).
% 31.57/20.41  tff(c_44333, plain, (![A_768]: (m1_pre_topc(k1_tsep_1(A_768, '#skF_5', '#skF_7'), '#skF_6') | ~m1_pre_topc('#skF_6', A_768) | ~v2_pre_topc(A_768) | ~m1_pre_topc('#skF_7', A_768) | ~m1_pre_topc('#skF_5', A_768) | ~l1_pre_topc(A_768) | v2_struct_0(A_768))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_44329])).
% 31.57/20.41  tff(c_50, plain, (~m1_pre_topc(k1_tsep_1('#skF_4', '#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 31.57/20.41  tff(c_44343, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_7', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44333, c_50])).
% 31.57/20.41  tff(c_44355, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_56, c_70, c_60, c_44343])).
% 31.57/20.41  tff(c_44357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_44355])).
% 31.57/20.41  tff(c_44359, plain, (~r1_tarski(k2_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')), k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_5749])).
% 31.57/20.41  tff(c_44418, plain, (![A_771]: (~r1_tarski(k2_struct_0(k1_tsep_1(A_771, '#skF_5', '#skF_7')), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', A_771) | ~m1_pre_topc('#skF_5', A_771) | ~l1_pre_topc(A_771) | v2_struct_0(A_771) | ~m1_pre_topc('#skF_7', A_771) | ~m1_pre_topc('#skF_5', A_771) | ~l1_pre_topc(A_771) | v2_struct_0(A_771))), inference(superposition, [status(thm), theory('equality')], [c_5796, c_44359])).
% 31.57/20.41  tff(c_44424, plain, (![A_771]: (~m1_pre_topc('#skF_7', A_771) | ~m1_pre_topc('#skF_5', A_771) | ~l1_pre_topc(A_771) | v2_struct_0(A_771) | ~m1_pre_topc(k1_tsep_1(A_771, '#skF_5', '#skF_7'), '#skF_6') | ~l1_pre_topc(k1_tsep_1(A_771, '#skF_5', '#skF_7')) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_22, c_44418])).
% 31.57/20.41  tff(c_44618, plain, (![A_774]: (~m1_pre_topc('#skF_7', A_774) | ~m1_pre_topc('#skF_5', A_774) | ~l1_pre_topc(A_774) | v2_struct_0(A_774) | ~m1_pre_topc(k1_tsep_1(A_774, '#skF_5', '#skF_7'), '#skF_6') | ~l1_pre_topc(k1_tsep_1(A_774, '#skF_5', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_44424])).
% 31.57/20.41  tff(c_44622, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_pre_topc('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_44618])).
% 31.57/20.41  tff(c_44625, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_5', '#skF_7')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_54, c_52, c_44622])).
% 31.57/20.41  tff(c_44626, plain, (~l1_pre_topc(k1_tsep_1('#skF_6', '#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_62, c_66, c_58, c_44625])).
% 31.57/20.41  tff(c_44629, plain, (~m1_pre_topc('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_322, c_44626])).
% 31.57/20.41  tff(c_44632, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_54, c_52, c_44629])).
% 31.57/20.41  tff(c_44634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_66, c_58, c_44632])).
% 31.57/20.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.57/20.41  
% 31.57/20.41  Inference rules
% 31.57/20.41  ----------------------
% 31.57/20.41  #Ref     : 2
% 31.57/20.41  #Sup     : 16155
% 31.57/20.41  #Fact    : 2
% 31.57/20.41  #Define  : 0
% 31.57/20.41  #Split   : 56
% 31.57/20.41  #Chain   : 0
% 31.57/20.41  #Close   : 0
% 31.57/20.41  
% 31.57/20.41  Ordering : KBO
% 31.57/20.41  
% 31.57/20.41  Simplification rules
% 31.57/20.41  ----------------------
% 31.57/20.41  #Subsume      : 1373
% 31.57/20.41  #Demod        : 1774
% 31.57/20.41  #Tautology    : 617
% 31.57/20.41  #SimpNegUnit  : 2116
% 31.57/20.41  #BackRed      : 0
% 31.57/20.41  
% 31.57/20.41  #Partial instantiations: 0
% 31.57/20.41  #Strategies tried      : 1
% 31.57/20.41  
% 31.57/20.41  Timing (in seconds)
% 31.57/20.41  ----------------------
% 31.57/20.41  Preprocessing        : 0.34
% 31.57/20.41  Parsing              : 0.16
% 31.57/20.41  CNF conversion       : 0.03
% 31.57/20.41  Main loop            : 19.28
% 31.57/20.41  Inferencing          : 2.76
% 31.57/20.41  Reduction            : 4.81
% 31.57/20.41  Demodulation         : 3.50
% 31.57/20.41  BG Simplification    : 0.55
% 31.57/20.41  Subsumption          : 10.22
% 31.57/20.41  Abstraction          : 0.56
% 31.57/20.41  MUC search           : 0.00
% 31.57/20.41  Cooper               : 0.00
% 31.57/20.41  Total                : 19.66
% 31.57/20.41  Index Insertion      : 0.00
% 31.57/20.41  Index Deletion       : 0.00
% 31.57/20.41  Index Matching       : 0.00
% 31.57/20.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
