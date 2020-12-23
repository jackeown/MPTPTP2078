%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:15 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 388 expanded)
%              Number of leaves         :   32 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  217 (1457 expanded)
%              Number of equality atoms :   20 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_75,axiom,(
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

tff(f_115,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C] :
                  ( r2_hidden(C,B)
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & A != B
        & k6_subset_1(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_103,plain,(
    ! [A_57,B_58] :
      ( '#skF_2'(A_57,B_58) != B_58
      | v3_tex_2(B_58,A_57)
      | ~ v2_tex_2(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_110,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_114,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_110])).

tff(c_115,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_114])).

tff(c_127,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_157,plain,(
    ! [B_65,A_66] :
      ( v2_tex_2(B_65,A_66)
      | ~ v1_zfmisc_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | v1_xboole_0(B_65)
      | ~ l1_pre_topc(A_66)
      | ~ v2_tdlat_3(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_167,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_157])).

tff(c_172,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_167])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_127,c_172])).

tff(c_175,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_176,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_179,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,'#skF_2'(A_68,B_67))
      | v3_tex_2(B_67,A_68)
      | ~ v2_tex_2(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_184,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_179])).

tff(c_188,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_176,c_184])).

tff(c_189,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_188])).

tff(c_28,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_192,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_28])).

tff(c_198,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_175,c_192])).

tff(c_202,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_206,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_202])).

tff(c_116,plain,(
    ! [A_59,B_60] :
      ( v2_tex_2('#skF_2'(A_59,B_60),A_59)
      | v3_tex_2(B_60,A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_125,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_121])).

tff(c_126,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_125])).

tff(c_178,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_126])).

tff(c_233,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1('#skF_2'(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | v3_tex_2(B_74,A_73)
      | ~ v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [B_31,A_29] :
      ( v1_zfmisc_1(B_31)
      | ~ v2_tex_2(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_29)
      | ~ v2_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_341,plain,(
    ! [A_100,B_101] :
      ( v1_zfmisc_1('#skF_2'(A_100,B_101))
      | ~ v2_tex_2('#skF_2'(A_100,B_101),A_100)
      | v1_xboole_0('#skF_2'(A_100,B_101))
      | ~ v2_tdlat_3(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100)
      | v3_tex_2(B_101,A_100)
      | ~ v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_233,c_32])).

tff(c_347,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_341])).

tff(c_354,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_176,c_42,c_40,c_347])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_206,c_202,c_354])).

tff(c_357,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_2,B_3] : m1_subset_1(k6_subset_1(A_2,B_3),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_43,A_44,B_45] :
      ( ~ v1_xboole_0(A_43)
      | ~ r2_hidden(A_44,k6_subset_1(A_43,B_45)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_80,plain,(
    ! [A_43,B_45] :
      ( ~ v1_xboole_0(A_43)
      | k6_subset_1(A_43,B_45) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_361,plain,(
    ! [B_45] : k6_subset_1('#skF_2'('#skF_3','#skF_4'),B_45) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_357,c_80])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( k6_subset_1(B_25,A_24) != k1_xboole_0
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_195,plain,
    ( k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0
    | '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_189,c_26])).

tff(c_201,plain,(
    k6_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_195])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_201])).

tff(c_366,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_365,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_406,plain,(
    ! [B_121,A_122] :
      ( v2_tex_2(B_121,A_122)
      | ~ v3_tex_2(B_121,A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_413,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_406])).

tff(c_417,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_365,c_413])).

tff(c_469,plain,(
    ! [B_133,A_134] :
      ( v1_zfmisc_1(B_133)
      | ~ v2_tex_2(B_133,A_134)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | v1_xboole_0(B_133)
      | ~ l1_pre_topc(A_134)
      | ~ v2_tdlat_3(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_479,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_469])).

tff(c_484,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_417,c_479])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_366,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k6_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.51/1.35  
% 2.51/1.35  %Foreground sorts:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Background operators:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Foreground operators:
% 2.51/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.51/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.35  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.51/1.35  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.51/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.35  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.51/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.51/1.35  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.51/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.51/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.35  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.51/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.35  
% 2.82/1.37  tff(f_135, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 2.82/1.37  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.82/1.37  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.82/1.37  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 2.82/1.37  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.82/1.37  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C]: (r2_hidden(C, B) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_mcart_1)).
% 2.82/1.37  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.82/1.37  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.82/1.37  tff(f_83, axiom, (![A, B]: ~((r1_tarski(A, B) & ~(A = B)) & (k6_subset_1(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_tex_2)).
% 2.82/1.37  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 2.82/1.37  tff(c_46, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_56, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 2.82/1.37  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.37  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_103, plain, (![A_57, B_58]: ('#skF_2'(A_57, B_58)!=B_58 | v3_tex_2(B_58, A_57) | ~v2_tex_2(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.37  tff(c_110, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_103])).
% 2.82/1.37  tff(c_114, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_110])).
% 2.82/1.37  tff(c_115, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_114])).
% 2.82/1.37  tff(c_127, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_115])).
% 2.82/1.37  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_40, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.82/1.37  tff(c_157, plain, (![B_65, A_66]: (v2_tex_2(B_65, A_66) | ~v1_zfmisc_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | v1_xboole_0(B_65) | ~l1_pre_topc(A_66) | ~v2_tdlat_3(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.37  tff(c_167, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_157])).
% 2.82/1.37  tff(c_172, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_167])).
% 2.82/1.37  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_127, c_172])).
% 2.82/1.37  tff(c_175, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 2.82/1.37  tff(c_176, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_115])).
% 2.82/1.37  tff(c_179, plain, (![B_67, A_68]: (r1_tarski(B_67, '#skF_2'(A_68, B_67)) | v3_tex_2(B_67, A_68) | ~v2_tex_2(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.37  tff(c_184, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_179])).
% 2.82/1.37  tff(c_188, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_176, c_184])).
% 2.82/1.37  tff(c_189, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_188])).
% 2.82/1.37  tff(c_28, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.82/1.37  tff(c_192, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_189, c_28])).
% 2.82/1.37  tff(c_198, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_175, c_192])).
% 2.82/1.37  tff(c_202, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_198])).
% 2.82/1.37  tff(c_206, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_202])).
% 2.82/1.37  tff(c_116, plain, (![A_59, B_60]: (v2_tex_2('#skF_2'(A_59, B_60), A_59) | v3_tex_2(B_60, A_59) | ~v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.37  tff(c_121, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_116])).
% 2.82/1.37  tff(c_125, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_121])).
% 2.82/1.37  tff(c_126, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_125])).
% 2.82/1.37  tff(c_178, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_126])).
% 2.82/1.37  tff(c_233, plain, (![A_73, B_74]: (m1_subset_1('#skF_2'(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | v3_tex_2(B_74, A_73) | ~v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.37  tff(c_32, plain, (![B_31, A_29]: (v1_zfmisc_1(B_31) | ~v2_tex_2(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_29) | ~v2_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.37  tff(c_341, plain, (![A_100, B_101]: (v1_zfmisc_1('#skF_2'(A_100, B_101)) | ~v2_tex_2('#skF_2'(A_100, B_101), A_100) | v1_xboole_0('#skF_2'(A_100, B_101)) | ~v2_tdlat_3(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100) | v3_tex_2(B_101, A_100) | ~v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_233, c_32])).
% 2.82/1.37  tff(c_347, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_178, c_341])).
% 2.82/1.37  tff(c_354, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_176, c_42, c_40, c_347])).
% 2.82/1.37  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_206, c_202, c_354])).
% 2.82/1.37  tff(c_357, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_198])).
% 2.82/1.37  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.37  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k6_subset_1(A_2, B_3), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.37  tff(c_66, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.37  tff(c_75, plain, (![A_43, A_44, B_45]: (~v1_xboole_0(A_43) | ~r2_hidden(A_44, k6_subset_1(A_43, B_45)))), inference(resolution, [status(thm)], [c_4, c_66])).
% 2.82/1.37  tff(c_80, plain, (![A_43, B_45]: (~v1_xboole_0(A_43) | k6_subset_1(A_43, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.82/1.37  tff(c_361, plain, (![B_45]: (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_357, c_80])).
% 2.82/1.37  tff(c_26, plain, (![B_25, A_24]: (k6_subset_1(B_25, A_24)!=k1_xboole_0 | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.82/1.37  tff(c_195, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0 | '#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_189, c_26])).
% 2.82/1.37  tff(c_201, plain, (k6_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_175, c_195])).
% 2.82/1.37  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_361, c_201])).
% 2.82/1.37  tff(c_366, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 2.82/1.37  tff(c_365, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.82/1.37  tff(c_406, plain, (![B_121, A_122]: (v2_tex_2(B_121, A_122) | ~v3_tex_2(B_121, A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.37  tff(c_413, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_406])).
% 2.82/1.37  tff(c_417, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_365, c_413])).
% 2.82/1.37  tff(c_469, plain, (![B_133, A_134]: (v1_zfmisc_1(B_133) | ~v2_tex_2(B_133, A_134) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_134))) | v1_xboole_0(B_133) | ~l1_pre_topc(A_134) | ~v2_tdlat_3(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.37  tff(c_479, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_469])).
% 2.82/1.37  tff(c_484, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_417, c_479])).
% 2.82/1.37  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_366, c_484])).
% 2.82/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.37  
% 2.82/1.37  Inference rules
% 2.82/1.37  ----------------------
% 2.82/1.37  #Ref     : 0
% 2.82/1.37  #Sup     : 78
% 2.82/1.37  #Fact    : 0
% 2.82/1.37  #Define  : 0
% 2.82/1.37  #Split   : 6
% 2.82/1.37  #Chain   : 0
% 2.82/1.37  #Close   : 0
% 2.82/1.37  
% 2.82/1.37  Ordering : KBO
% 2.82/1.37  
% 2.82/1.37  Simplification rules
% 2.82/1.37  ----------------------
% 2.82/1.37  #Subsume      : 12
% 2.82/1.37  #Demod        : 58
% 2.82/1.37  #Tautology    : 12
% 2.82/1.37  #SimpNegUnit  : 15
% 2.82/1.37  #BackRed      : 1
% 2.82/1.37  
% 2.82/1.37  #Partial instantiations: 0
% 2.82/1.37  #Strategies tried      : 1
% 2.82/1.37  
% 2.82/1.37  Timing (in seconds)
% 2.82/1.37  ----------------------
% 2.82/1.38  Preprocessing        : 0.29
% 2.82/1.38  Parsing              : 0.16
% 2.82/1.38  CNF conversion       : 0.02
% 2.82/1.38  Main loop            : 0.30
% 2.82/1.38  Inferencing          : 0.12
% 2.82/1.38  Reduction            : 0.08
% 2.82/1.38  Demodulation         : 0.05
% 2.82/1.38  BG Simplification    : 0.02
% 2.82/1.38  Subsumption          : 0.06
% 2.82/1.38  Abstraction          : 0.01
% 2.82/1.38  MUC search           : 0.00
% 2.82/1.38  Cooper               : 0.00
% 2.82/1.38  Total                : 0.64
% 2.82/1.38  Index Insertion      : 0.00
% 2.82/1.38  Index Deletion       : 0.00
% 2.82/1.38  Index Matching       : 0.00
% 2.82/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
