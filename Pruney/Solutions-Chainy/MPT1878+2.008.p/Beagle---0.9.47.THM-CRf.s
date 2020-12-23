%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 11.77s
% Output     : CNFRefutation 11.77s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 129 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  185 ( 333 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_109,axiom,(
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

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_58,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_1'(A_44),A_44)
      | A_44 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_44] :
      ( m1_subset_1('#skF_1'(A_44),A_44)
      | A_44 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_88,c_16])).

tff(c_145,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_152,plain,(
    ! [A_44] :
      ( k6_domain_1(A_44,'#skF_1'(A_44)) = k1_tarski('#skF_1'(A_44))
      | v1_xboole_0(A_44)
      | A_44 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_92,c_145])).

tff(c_42,plain,(
    ! [A_31,B_33] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_31),B_33),A_31)
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k6_domain_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [A_6] : m1_subset_1('#skF_5',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_12])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [A_4] : r1_tarski('#skF_5',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_8])).

tff(c_587,plain,(
    ! [C_98,B_99,A_100] :
      ( C_98 = B_99
      | ~ r1_tarski(B_99,C_98)
      | ~ v2_tex_2(C_98,A_100)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_589,plain,(
    ! [A_4,A_100] :
      ( A_4 = '#skF_5'
      | ~ v2_tex_2(A_4,A_100)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2('#skF_5',A_100)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_70,c_587])).

tff(c_822,plain,(
    ! [A_109,A_110] :
      ( A_109 = '#skF_5'
      | ~ v2_tex_2(A_109,A_110)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ v3_tex_2('#skF_5',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_589])).

tff(c_5511,plain,(
    ! [A_220,B_221] :
      ( k6_domain_1(u1_struct_0(A_220),B_221) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_220),B_221),A_220)
      | ~ v3_tex_2('#skF_5',A_220)
      | ~ l1_pre_topc(A_220)
      | ~ m1_subset_1(B_221,u1_struct_0(A_220))
      | v1_xboole_0(u1_struct_0(A_220)) ) ),
    inference(resolution,[status(thm)],[c_26,c_822])).

tff(c_5531,plain,(
    ! [A_222,B_223] :
      ( k6_domain_1(u1_struct_0(A_222),B_223) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_222)
      | v1_xboole_0(u1_struct_0(A_222))
      | ~ m1_subset_1(B_223,u1_struct_0(A_222))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_42,c_5511])).

tff(c_5623,plain,(
    ! [A_227] :
      ( k6_domain_1(u1_struct_0(A_227),'#skF_1'(u1_struct_0(A_227))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_227)
      | v1_xboole_0(u1_struct_0(A_227))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227)
      | u1_struct_0(A_227) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_92,c_5531])).

tff(c_16951,plain,(
    ! [A_386] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_386))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_386)
      | v1_xboole_0(u1_struct_0(A_386))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386)
      | u1_struct_0(A_386) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_386))
      | u1_struct_0(A_386) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_5623])).

tff(c_10,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17117,plain,(
    ! [A_386] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ v3_tex_2('#skF_5',A_386)
      | v1_xboole_0(u1_struct_0(A_386))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386)
      | u1_struct_0(A_386) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_386))
      | u1_struct_0(A_386) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16951,c_10])).

tff(c_17167,plain,(
    ! [A_390] :
      ( ~ v3_tex_2('#skF_5',A_390)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390)
      | v1_xboole_0(u1_struct_0(A_390))
      | u1_struct_0(A_390) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_17117])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_4])).

tff(c_17180,plain,(
    ! [A_391] :
      ( ~ v3_tex_2('#skF_5',A_391)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391)
      | u1_struct_0(A_391) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_17167,c_68])).

tff(c_17186,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_17180])).

tff(c_17190,plain,
    ( v2_struct_0('#skF_4')
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_17186])).

tff(c_17191,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_17190])).

tff(c_186,plain,(
    ! [A_63] :
      ( m1_subset_1('#skF_2'(A_63),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_197,plain,(
    ! [A_63] :
      ( v1_xboole_0('#skF_2'(A_63))
      | ~ v1_xboole_0(u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_186,c_14])).

tff(c_17308,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17191,c_197])).

tff(c_17409,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_17308])).

tff(c_17410,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_17409])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_2'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_17417,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_17410,c_22])).

tff(c_17423,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_17417])).

tff(c_17425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_17423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:59:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.77/5.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.77/5.04  
% 11.77/5.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.77/5.04  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 11.77/5.04  
% 11.77/5.04  %Foreground sorts:
% 11.77/5.04  
% 11.77/5.04  
% 11.77/5.04  %Background operators:
% 11.77/5.04  
% 11.77/5.04  
% 11.77/5.04  %Foreground operators:
% 11.77/5.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.77/5.04  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.77/5.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.77/5.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.77/5.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.77/5.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.77/5.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.77/5.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.77/5.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.77/5.04  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.77/5.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.77/5.04  tff('#skF_5', type, '#skF_5': $i).
% 11.77/5.04  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 11.77/5.04  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 11.77/5.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.77/5.04  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.77/5.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.77/5.04  tff('#skF_4', type, '#skF_4': $i).
% 11.77/5.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.77/5.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.77/5.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.77/5.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.77/5.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.77/5.04  
% 11.77/5.05  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 11.77/5.05  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.77/5.05  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.77/5.05  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 11.77/5.05  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.77/5.05  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 11.77/5.05  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 11.77/5.05  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.77/5.05  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.77/5.05  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 11.77/5.05  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 11.77/5.05  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 11.77/5.05  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.77/5.05  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.77/5.05  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.77/5.05  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.77/5.05  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.77/5.05  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.77/5.05  tff(c_58, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_30])).
% 11.77/5.05  tff(c_67, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_58])).
% 11.77/5.05  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.77/5.05  tff(c_88, plain, (![A_44]: (r2_hidden('#skF_1'(A_44), A_44) | A_44='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_6])).
% 11.77/5.05  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.77/5.05  tff(c_92, plain, (![A_44]: (m1_subset_1('#skF_1'(A_44), A_44) | A_44='#skF_5')), inference(resolution, [status(thm)], [c_88, c_16])).
% 11.77/5.05  tff(c_145, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.77/5.05  tff(c_152, plain, (![A_44]: (k6_domain_1(A_44, '#skF_1'(A_44))=k1_tarski('#skF_1'(A_44)) | v1_xboole_0(A_44) | A_44='#skF_5')), inference(resolution, [status(thm)], [c_92, c_145])).
% 11.77/5.05  tff(c_42, plain, (![A_31, B_33]: (v2_tex_2(k6_domain_1(u1_struct_0(A_31), B_33), A_31) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.77/5.05  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(k6_domain_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.77/5.05  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.77/5.05  tff(c_69, plain, (![A_6]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_12])).
% 11.77/5.05  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.77/5.05  tff(c_70, plain, (![A_4]: (r1_tarski('#skF_5', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_8])).
% 11.77/5.05  tff(c_587, plain, (![C_98, B_99, A_100]: (C_98=B_99 | ~r1_tarski(B_99, C_98) | ~v2_tex_2(C_98, A_100) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.77/5.05  tff(c_589, plain, (![A_4, A_100]: (A_4='#skF_5' | ~v2_tex_2(A_4, A_100) | ~m1_subset_1(A_4, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2('#skF_5', A_100) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_70, c_587])).
% 11.77/5.05  tff(c_822, plain, (![A_109, A_110]: (A_109='#skF_5' | ~v2_tex_2(A_109, A_110) | ~m1_subset_1(A_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~v3_tex_2('#skF_5', A_110) | ~l1_pre_topc(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_589])).
% 11.77/5.05  tff(c_5511, plain, (![A_220, B_221]: (k6_domain_1(u1_struct_0(A_220), B_221)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_220), B_221), A_220) | ~v3_tex_2('#skF_5', A_220) | ~l1_pre_topc(A_220) | ~m1_subset_1(B_221, u1_struct_0(A_220)) | v1_xboole_0(u1_struct_0(A_220)))), inference(resolution, [status(thm)], [c_26, c_822])).
% 11.77/5.05  tff(c_5531, plain, (![A_222, B_223]: (k6_domain_1(u1_struct_0(A_222), B_223)='#skF_5' | ~v3_tex_2('#skF_5', A_222) | v1_xboole_0(u1_struct_0(A_222)) | ~m1_subset_1(B_223, u1_struct_0(A_222)) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_42, c_5511])).
% 11.77/5.05  tff(c_5623, plain, (![A_227]: (k6_domain_1(u1_struct_0(A_227), '#skF_1'(u1_struct_0(A_227)))='#skF_5' | ~v3_tex_2('#skF_5', A_227) | v1_xboole_0(u1_struct_0(A_227)) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227) | u1_struct_0(A_227)='#skF_5')), inference(resolution, [status(thm)], [c_92, c_5531])).
% 11.77/5.05  tff(c_16951, plain, (![A_386]: (k1_tarski('#skF_1'(u1_struct_0(A_386)))='#skF_5' | ~v3_tex_2('#skF_5', A_386) | v1_xboole_0(u1_struct_0(A_386)) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386) | u1_struct_0(A_386)='#skF_5' | v1_xboole_0(u1_struct_0(A_386)) | u1_struct_0(A_386)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_152, c_5623])).
% 11.77/5.05  tff(c_10, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.77/5.05  tff(c_17117, plain, (![A_386]: (~v1_xboole_0('#skF_5') | ~v3_tex_2('#skF_5', A_386) | v1_xboole_0(u1_struct_0(A_386)) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386) | u1_struct_0(A_386)='#skF_5' | v1_xboole_0(u1_struct_0(A_386)) | u1_struct_0(A_386)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16951, c_10])).
% 11.77/5.05  tff(c_17167, plain, (![A_390]: (~v3_tex_2('#skF_5', A_390) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390) | v1_xboole_0(u1_struct_0(A_390)) | u1_struct_0(A_390)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_17117])).
% 11.77/5.05  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 11.77/5.05  tff(c_68, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_4])).
% 11.77/5.05  tff(c_17180, plain, (![A_391]: (~v3_tex_2('#skF_5', A_391) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391) | u1_struct_0(A_391)='#skF_5')), inference(resolution, [status(thm)], [c_17167, c_68])).
% 11.77/5.05  tff(c_17186, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_17180])).
% 11.77/5.05  tff(c_17190, plain, (v2_struct_0('#skF_4') | u1_struct_0('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_17186])).
% 11.77/5.05  tff(c_17191, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_17190])).
% 11.77/5.05  tff(c_186, plain, (![A_63]: (m1_subset_1('#skF_2'(A_63), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.77/5.05  tff(c_14, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.77/5.05  tff(c_197, plain, (![A_63]: (v1_xboole_0('#skF_2'(A_63)) | ~v1_xboole_0(u1_struct_0(A_63)) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_186, c_14])).
% 11.77/5.05  tff(c_17308, plain, (v1_xboole_0('#skF_2'('#skF_4')) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17191, c_197])).
% 11.77/5.05  tff(c_17409, plain, (v1_xboole_0('#skF_2'('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_17308])).
% 11.77/5.05  tff(c_17410, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_17409])).
% 11.77/5.05  tff(c_22, plain, (![A_15]: (~v1_xboole_0('#skF_2'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.77/5.05  tff(c_17417, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_17410, c_22])).
% 11.77/5.05  tff(c_17423, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_17417])).
% 11.77/5.05  tff(c_17425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_17423])).
% 11.77/5.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.77/5.05  
% 11.77/5.05  Inference rules
% 11.77/5.05  ----------------------
% 11.77/5.05  #Ref     : 0
% 11.77/5.05  #Sup     : 3972
% 11.77/5.05  #Fact    : 0
% 11.77/5.05  #Define  : 0
% 11.77/5.05  #Split   : 12
% 11.77/5.05  #Chain   : 0
% 11.77/5.05  #Close   : 0
% 11.77/5.05  
% 11.77/5.05  Ordering : KBO
% 11.77/5.05  
% 11.77/5.05  Simplification rules
% 11.77/5.05  ----------------------
% 11.77/5.05  #Subsume      : 770
% 11.77/5.05  #Demod        : 6226
% 11.77/5.05  #Tautology    : 1787
% 11.77/5.05  #SimpNegUnit  : 1151
% 11.77/5.05  #BackRed      : 24
% 11.77/5.05  
% 11.77/5.05  #Partial instantiations: 0
% 11.77/5.05  #Strategies tried      : 1
% 11.77/5.05  
% 11.77/5.05  Timing (in seconds)
% 11.77/5.05  ----------------------
% 11.77/5.06  Preprocessing        : 0.32
% 11.77/5.06  Parsing              : 0.17
% 11.77/5.06  CNF conversion       : 0.02
% 11.77/5.06  Main loop            : 3.98
% 11.77/5.06  Inferencing          : 0.87
% 11.77/5.06  Reduction            : 1.19
% 11.77/5.06  Demodulation         : 0.83
% 11.77/5.06  BG Simplification    : 0.12
% 11.77/5.06  Subsumption          : 1.63
% 11.77/5.06  Abstraction          : 0.16
% 11.77/5.06  MUC search           : 0.00
% 11.77/5.06  Cooper               : 0.00
% 11.77/5.06  Total                : 4.33
% 11.77/5.06  Index Insertion      : 0.00
% 11.77/5.06  Index Deletion       : 0.00
% 11.77/5.06  Index Matching       : 0.00
% 11.77/5.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
