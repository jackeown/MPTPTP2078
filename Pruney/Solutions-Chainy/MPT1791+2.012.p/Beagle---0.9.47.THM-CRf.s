%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:50 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 556 expanded)
%              Number of leaves         :   33 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          :  252 (1818 expanded)
%              Number of equality atoms :   51 ( 226 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > o_0_0_xboole_0 > k6_numbers > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k6_numbers,type,(
    k6_numbers: $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tops_1(B,A) )
           => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_70,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_115,plain,(
    ! [B_43,A_44] :
      ( v3_pre_topc(B_43,A_44)
      | ~ r2_hidden(B_43,u1_pre_topc(A_44))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_125,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_121])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_125])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_447,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(B_62,u1_pre_topc(A_63))
      | k5_tmap_1(A_63,B_62) != u1_pre_topc(A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_465,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_447])).

tff(c_474,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_465])).

tff(c_475,plain,(
    k5_tmap_1('#skF_2','#skF_3') != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_126,c_474])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_72,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_50])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_xboole_0('#skF_1'(A_15))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_1'(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_89,plain,(
    ! [B_36,A_37] :
      ( v3_pre_topc(B_36,A_37)
      | ~ v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,(
    ! [A_15] :
      ( v3_pre_topc('#skF_1'(A_15),A_15)
      | ~ v1_xboole_0('#skF_1'(A_15))
      | ~ v2_pre_topc(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_77,plain,(
    ! [B_34,A_35] :
      ( v3_tops_1(B_34,A_35)
      | ~ v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,(
    ! [A_15] :
      ( v3_tops_1('#skF_1'(A_15),A_15)
      | ~ v1_xboole_0('#skF_1'(A_15))
      | ~ v2_pre_topc(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_77])).

tff(c_210,plain,(
    ! [B_52,A_53] :
      ( k1_xboole_0 = B_52
      | ~ v3_tops_1(B_52,A_53)
      | ~ v3_pre_topc(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_227,plain,(
    ! [A_54] :
      ( '#skF_1'(A_54) = k1_xboole_0
      | ~ v3_tops_1('#skF_1'(A_54),A_54)
      | ~ v3_pre_topc('#skF_1'(A_54),A_54)
      | ~ v2_pre_topc(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_22,c_210])).

tff(c_263,plain,(
    ! [A_57] :
      ( '#skF_1'(A_57) = k1_xboole_0
      | ~ v3_pre_topc('#skF_1'(A_57),A_57)
      | ~ v1_xboole_0('#skF_1'(A_57))
      | ~ v2_pre_topc(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_84,c_227])).

tff(c_268,plain,(
    ! [A_58] :
      ( '#skF_1'(A_58) = k1_xboole_0
      | ~ v1_xboole_0('#skF_1'(A_58))
      | ~ v2_pre_topc(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_96,c_263])).

tff(c_273,plain,(
    ! [A_59] :
      ( '#skF_1'(A_59) = k1_xboole_0
      | ~ v2_pre_topc(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_20,c_268])).

tff(c_276,plain,
    ( '#skF_1'('#skF_2') = k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_273])).

tff(c_279,plain,(
    '#skF_1'('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_276])).

tff(c_307,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_20])).

tff(c_330,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_307])).

tff(c_304,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_22])).

tff(c_328,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_304])).

tff(c_12,plain,(
    ! [B_8,A_6] :
      ( v3_pre_topc(B_8,A_6)
      | ~ v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_351,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_2')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_12])).

tff(c_379,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_330,c_351])).

tff(c_102,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,u1_pre_topc(A_40))
      | ~ v3_pre_topc(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),u1_pre_topc(A_15))
      | ~ v3_pre_topc('#skF_1'(A_15),A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_295,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_109])).

tff(c_322,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_279,c_295])).

tff(c_446,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_322])).

tff(c_505,plain,(
    ! [A_64,B_65] :
      ( k5_tmap_1(A_64,B_65) = u1_pre_topc(A_64)
      | ~ r2_hidden(B_65,u1_pre_topc(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_511,plain,
    ( k5_tmap_1('#skF_2',k1_xboole_0) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_505])).

tff(c_527,plain,
    ( k5_tmap_1('#skF_2',k1_xboole_0) = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_446,c_511])).

tff(c_528,plain,(
    k5_tmap_1('#skF_2',k1_xboole_0) = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_527])).

tff(c_383,plain,(
    ! [A_60,B_61] :
      ( g1_pre_topc(u1_struct_0(A_60),k5_tmap_1(A_60,B_61)) = k6_tmap_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_385,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2',k1_xboole_0)) = k6_tmap_1('#skF_2',k1_xboole_0)
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_383])).

tff(c_396,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2',k1_xboole_0)) = k6_tmap_1('#skF_2',k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_385])).

tff(c_397,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2',k1_xboole_0)) = k6_tmap_1('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_396])).

tff(c_535,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_397])).

tff(c_538,plain,(
    k6_tmap_1('#skF_2',k1_xboole_0) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_535])).

tff(c_32,plain,(
    ! [A_26,B_28] :
      ( u1_pre_topc(k6_tmap_1(A_26,B_28)) = k5_tmap_1(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_334,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2',k1_xboole_0)) = k5_tmap_1('#skF_2',k1_xboole_0)
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_32])).

tff(c_357,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2',k1_xboole_0)) = k5_tmap_1('#skF_2',k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_334])).

tff(c_358,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k1_xboole_0)) = k5_tmap_1('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_357])).

tff(c_536,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k1_xboole_0)) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_358])).

tff(c_558,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_536])).

tff(c_232,plain,(
    ! [A_55,B_56] :
      ( u1_pre_topc(k6_tmap_1(A_55,B_56)) = k5_tmap_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_244,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_232])).

tff(c_248,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_244])).

tff(c_249,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_248])).

tff(c_567,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_249])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_567])).

tff(c_570,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_571,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_612,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(B_76,u1_pre_topc(A_77))
      | ~ v3_pre_topc(B_76,A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_618,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_612])).

tff(c_622,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_571,c_618])).

tff(c_941,plain,(
    ! [A_95,B_96] :
      ( k5_tmap_1(A_95,B_96) = u1_pre_topc(A_95)
      | ~ r2_hidden(B_96,u1_pre_topc(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_959,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_3',u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_941])).

tff(c_968,plain,
    ( k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_622,c_959])).

tff(c_969,plain,(
    k5_tmap_1('#skF_2','#skF_3') = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_968])).

tff(c_829,plain,(
    ! [A_93,B_94] :
      ( g1_pre_topc(u1_struct_0(A_93),k5_tmap_1(A_93,B_94)) = k6_tmap_1(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_837,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_829])).

tff(c_842,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_837])).

tff(c_843,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_3')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_842])).

tff(c_1016,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_843])).

tff(c_1017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_1016])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.59  
% 3.23/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.59  %$ v3_tops_1 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > o_0_0_xboole_0 > k6_numbers > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.23/1.59  
% 3.23/1.59  %Foreground sorts:
% 3.23/1.59  
% 3.23/1.59  
% 3.23/1.59  %Background operators:
% 3.23/1.59  
% 3.23/1.59  
% 3.23/1.59  %Foreground operators:
% 3.23/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.59  tff(k6_numbers, type, k6_numbers: $i).
% 3.23/1.59  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.23/1.59  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.23/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.59  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.23/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.59  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.23/1.59  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.23/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.59  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.23/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.23/1.59  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.23/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.59  
% 3.23/1.61  tff(f_153, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.23/1.61  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.23/1.61  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.23/1.61  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_connsp_1)).
% 3.23/1.61  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.23/1.61  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_tops_1)).
% 3.23/1.61  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 3.23/1.61  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.23/1.61  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.23/1.61  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.61  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.61  tff(c_70, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 3.23/1.61  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.61  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.61  tff(c_115, plain, (![B_43, A_44]: (v3_pre_topc(B_43, A_44) | ~r2_hidden(B_43, u1_pre_topc(A_44)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.61  tff(c_121, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_115])).
% 3.23/1.61  tff(c_125, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_121])).
% 3.23/1.61  tff(c_126, plain, (~r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_125])).
% 3.23/1.61  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.61  tff(c_447, plain, (![B_62, A_63]: (r2_hidden(B_62, u1_pre_topc(A_63)) | k5_tmap_1(A_63, B_62)!=u1_pre_topc(A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.23/1.61  tff(c_465, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_447])).
% 3.23/1.61  tff(c_474, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_465])).
% 3.23/1.61  tff(c_475, plain, (k5_tmap_1('#skF_2', '#skF_3')!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_126, c_474])).
% 3.23/1.61  tff(c_50, plain, (v3_pre_topc('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.23/1.61  tff(c_72, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_50])).
% 3.23/1.61  tff(c_20, plain, (![A_15]: (v1_xboole_0('#skF_1'(A_15)) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.23/1.61  tff(c_22, plain, (![A_15]: (m1_subset_1('#skF_1'(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.23/1.61  tff(c_89, plain, (![B_36, A_37]: (v3_pre_topc(B_36, A_37) | ~v1_xboole_0(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.61  tff(c_96, plain, (![A_15]: (v3_pre_topc('#skF_1'(A_15), A_15) | ~v1_xboole_0('#skF_1'(A_15)) | ~v2_pre_topc(A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_22, c_89])).
% 3.23/1.61  tff(c_77, plain, (![B_34, A_35]: (v3_tops_1(B_34, A_35) | ~v1_xboole_0(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.61  tff(c_84, plain, (![A_15]: (v3_tops_1('#skF_1'(A_15), A_15) | ~v1_xboole_0('#skF_1'(A_15)) | ~v2_pre_topc(A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_22, c_77])).
% 3.23/1.61  tff(c_210, plain, (![B_52, A_53]: (k1_xboole_0=B_52 | ~v3_tops_1(B_52, A_53) | ~v3_pre_topc(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/1.61  tff(c_227, plain, (![A_54]: ('#skF_1'(A_54)=k1_xboole_0 | ~v3_tops_1('#skF_1'(A_54), A_54) | ~v3_pre_topc('#skF_1'(A_54), A_54) | ~v2_pre_topc(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_22, c_210])).
% 3.23/1.61  tff(c_263, plain, (![A_57]: ('#skF_1'(A_57)=k1_xboole_0 | ~v3_pre_topc('#skF_1'(A_57), A_57) | ~v1_xboole_0('#skF_1'(A_57)) | ~v2_pre_topc(A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_84, c_227])).
% 3.23/1.61  tff(c_268, plain, (![A_58]: ('#skF_1'(A_58)=k1_xboole_0 | ~v1_xboole_0('#skF_1'(A_58)) | ~v2_pre_topc(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_96, c_263])).
% 3.23/1.61  tff(c_273, plain, (![A_59]: ('#skF_1'(A_59)=k1_xboole_0 | ~v2_pre_topc(A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_20, c_268])).
% 3.23/1.61  tff(c_276, plain, ('#skF_1'('#skF_2')=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_273])).
% 3.23/1.61  tff(c_279, plain, ('#skF_1'('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_276])).
% 3.23/1.61  tff(c_307, plain, (v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_279, c_20])).
% 3.23/1.61  tff(c_330, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_307])).
% 3.23/1.61  tff(c_304, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_279, c_22])).
% 3.23/1.61  tff(c_328, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_304])).
% 3.23/1.61  tff(c_12, plain, (![B_8, A_6]: (v3_pre_topc(B_8, A_6) | ~v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.23/1.61  tff(c_351, plain, (v3_pre_topc(k1_xboole_0, '#skF_2') | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_328, c_12])).
% 3.23/1.61  tff(c_379, plain, (v3_pre_topc(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_330, c_351])).
% 3.23/1.61  tff(c_102, plain, (![B_39, A_40]: (r2_hidden(B_39, u1_pre_topc(A_40)) | ~v3_pre_topc(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.61  tff(c_109, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), u1_pre_topc(A_15)) | ~v3_pre_topc('#skF_1'(A_15), A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_22, c_102])).
% 3.23/1.61  tff(c_295, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_279, c_109])).
% 3.23/1.61  tff(c_322, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_2')) | ~v3_pre_topc(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_279, c_295])).
% 3.23/1.61  tff(c_446, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_322])).
% 3.23/1.61  tff(c_505, plain, (![A_64, B_65]: (k5_tmap_1(A_64, B_65)=u1_pre_topc(A_64) | ~r2_hidden(B_65, u1_pre_topc(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.23/1.61  tff(c_511, plain, (k5_tmap_1('#skF_2', k1_xboole_0)=u1_pre_topc('#skF_2') | ~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_328, c_505])).
% 3.23/1.61  tff(c_527, plain, (k5_tmap_1('#skF_2', k1_xboole_0)=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_446, c_511])).
% 3.23/1.61  tff(c_528, plain, (k5_tmap_1('#skF_2', k1_xboole_0)=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_527])).
% 3.23/1.61  tff(c_383, plain, (![A_60, B_61]: (g1_pre_topc(u1_struct_0(A_60), k5_tmap_1(A_60, B_61))=k6_tmap_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.61  tff(c_385, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', k1_xboole_0))=k6_tmap_1('#skF_2', k1_xboole_0) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_328, c_383])).
% 3.23/1.61  tff(c_396, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', k1_xboole_0))=k6_tmap_1('#skF_2', k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_385])).
% 3.23/1.61  tff(c_397, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', k1_xboole_0))=k6_tmap_1('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_42, c_396])).
% 3.23/1.61  tff(c_535, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_528, c_397])).
% 3.23/1.61  tff(c_538, plain, (k6_tmap_1('#skF_2', k1_xboole_0)=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_535])).
% 3.23/1.61  tff(c_32, plain, (![A_26, B_28]: (u1_pre_topc(k6_tmap_1(A_26, B_28))=k5_tmap_1(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.23/1.61  tff(c_334, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k1_xboole_0))=k5_tmap_1('#skF_2', k1_xboole_0) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_328, c_32])).
% 3.23/1.61  tff(c_357, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k1_xboole_0))=k5_tmap_1('#skF_2', k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_334])).
% 3.23/1.61  tff(c_358, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k1_xboole_0))=k5_tmap_1('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_42, c_357])).
% 3.23/1.61  tff(c_536, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k1_xboole_0))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_528, c_358])).
% 3.23/1.61  tff(c_558, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_536])).
% 3.23/1.61  tff(c_232, plain, (![A_55, B_56]: (u1_pre_topc(k6_tmap_1(A_55, B_56))=k5_tmap_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.23/1.61  tff(c_244, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_232])).
% 3.23/1.61  tff(c_248, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_244])).
% 3.23/1.61  tff(c_249, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))=k5_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_248])).
% 3.23/1.61  tff(c_567, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_249])).
% 3.23/1.61  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_475, c_567])).
% 3.23/1.61  tff(c_570, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.23/1.61  tff(c_571, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 3.23/1.61  tff(c_612, plain, (![B_76, A_77]: (r2_hidden(B_76, u1_pre_topc(A_77)) | ~v3_pre_topc(B_76, A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.61  tff(c_618, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_612])).
% 3.23/1.61  tff(c_622, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_571, c_618])).
% 3.23/1.61  tff(c_941, plain, (![A_95, B_96]: (k5_tmap_1(A_95, B_96)=u1_pre_topc(A_95) | ~r2_hidden(B_96, u1_pre_topc(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.23/1.61  tff(c_959, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | ~r2_hidden('#skF_3', u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_941])).
% 3.23/1.61  tff(c_968, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_622, c_959])).
% 3.23/1.61  tff(c_969, plain, (k5_tmap_1('#skF_2', '#skF_3')=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_968])).
% 3.23/1.61  tff(c_829, plain, (![A_93, B_94]: (g1_pre_topc(u1_struct_0(A_93), k5_tmap_1(A_93, B_94))=k6_tmap_1(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.61  tff(c_837, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_829])).
% 3.23/1.61  tff(c_842, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_837])).
% 3.23/1.61  tff(c_843, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_3'))=k6_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_842])).
% 3.23/1.61  tff(c_1016, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_843])).
% 3.23/1.61  tff(c_1017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_1016])).
% 3.23/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.61  
% 3.23/1.61  Inference rules
% 3.23/1.61  ----------------------
% 3.23/1.61  #Ref     : 0
% 3.23/1.61  #Sup     : 226
% 3.23/1.61  #Fact    : 0
% 3.23/1.61  #Define  : 0
% 3.23/1.61  #Split   : 7
% 3.23/1.61  #Chain   : 0
% 3.23/1.61  #Close   : 0
% 3.23/1.61  
% 3.23/1.61  Ordering : KBO
% 3.23/1.61  
% 3.23/1.61  Simplification rules
% 3.23/1.61  ----------------------
% 3.23/1.61  #Subsume      : 37
% 3.23/1.61  #Demod        : 198
% 3.23/1.61  #Tautology    : 79
% 3.23/1.61  #SimpNegUnit  : 34
% 3.23/1.61  #BackRed      : 10
% 3.23/1.61  
% 3.23/1.61  #Partial instantiations: 0
% 3.23/1.61  #Strategies tried      : 1
% 3.23/1.61  
% 3.23/1.61  Timing (in seconds)
% 3.23/1.61  ----------------------
% 3.23/1.62  Preprocessing        : 0.39
% 3.23/1.62  Parsing              : 0.21
% 3.23/1.62  CNF conversion       : 0.03
% 3.23/1.62  Main loop            : 0.42
% 3.23/1.62  Inferencing          : 0.15
% 3.23/1.62  Reduction            : 0.14
% 3.23/1.62  Demodulation         : 0.09
% 3.23/1.62  BG Simplification    : 0.03
% 3.23/1.62  Subsumption          : 0.07
% 3.23/1.62  Abstraction          : 0.02
% 3.23/1.62  MUC search           : 0.00
% 3.23/1.62  Cooper               : 0.00
% 3.23/1.62  Total                : 0.86
% 3.62/1.62  Index Insertion      : 0.00
% 3.62/1.62  Index Deletion       : 0.00
% 3.62/1.62  Index Matching       : 0.00
% 3.62/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
