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
% DateTime   : Thu Dec  3 10:30:23 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 130 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  185 ( 514 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_18,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16,plain,(
    ! [A_13,B_21] :
      ( m1_subset_1('#skF_1'(A_13,B_21),u1_struct_0(A_13))
      | v2_tex_2(B_21,A_13)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v3_tdlat_3(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_116,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_50)
      | v2_tex_2(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v3_tdlat_3(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_123,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_128,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_123])).

tff(c_129,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_128])).

tff(c_31,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_31])).

tff(c_36,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_35])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k6_domain_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_37,B_38] :
      ( v4_pre_topc(k2_pre_topc(A_37,B_38),A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    ! [A_37,B_7] :
      ( v4_pre_topc(k2_pre_topc(A_37,k6_domain_1(u1_struct_0(A_37),B_7)),A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | ~ m1_subset_1(B_7,u1_struct_0(A_37))
      | v1_xboole_0(u1_struct_0(A_37)) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k2_pre_topc(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [C_31] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31))) = k6_domain_1(u1_struct_0('#skF_2'),C_31)
      | ~ r2_hidden(C_31,'#skF_3')
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_150,plain,(
    ! [A_63,B_64,D_65] :
      ( k9_subset_1(u1_struct_0(A_63),B_64,D_65) != k6_domain_1(u1_struct_0(A_63),'#skF_1'(A_63,B_64))
      | ~ v4_pre_topc(D_65,A_63)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v3_tdlat_3(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_152,plain,(
    ! [C_31] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_31) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_31,'#skF_3')
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_154,plain,(
    ! [C_31] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_31) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_31)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(C_31,'#skF_3')
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_152])).

tff(c_159,plain,(
    ! [C_72] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_72) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_72)),'#skF_2')
      | ~ m1_subset_1(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_72)),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_72,'#skF_3')
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_154])).

tff(c_162,plain,(
    ! [C_72] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_72) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_72)),'#skF_2')
      | ~ r2_hidden(C_72,'#skF_3')
      | ~ m1_subset_1(C_72,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_72),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_166,plain,(
    ! [C_73] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_73) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_73)),'#skF_2')
      | ~ r2_hidden(C_73,'#skF_3')
      | ~ m1_subset_1(C_73,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),C_73),k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_162])).

tff(c_170,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_7)),'#skF_2')
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_174,plain,(
    ! [B_74] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_74) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_74)),'#skF_2')
      | ~ r2_hidden(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_170])).

tff(c_178,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_57,c_174])).

tff(c_181,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_178])).

tff(c_182,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),B_7) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_181])).

tff(c_185,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_182])).

tff(c_187,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_185])).

tff(c_191,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_187])).

tff(c_194,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_194])).

tff(c_197,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_231,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v1_xboole_0(B_83)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_241,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_231])).

tff(c_246,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_197,c_241])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_18,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  
% 2.27/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  %$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.27  
% 2.27/1.27  %Foreground sorts:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Background operators:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Foreground operators:
% 2.27/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.27/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.27/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.27  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.27/1.27  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.27/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.27/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.27/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.27  
% 2.27/1.28  tff(f_117, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 2.27/1.28  tff(f_95, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 2.27/1.28  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.27/1.28  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.27/1.28  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.27/1.28  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.27/1.28  tff(f_67, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.27/1.28  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_18, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_26, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_16, plain, (![A_13, B_21]: (m1_subset_1('#skF_1'(A_13, B_21), u1_struct_0(A_13)) | v2_tex_2(B_21, A_13) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13) | ~v3_tdlat_3(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.27/1.28  tff(c_116, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), B_50) | v2_tex_2(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v3_tdlat_3(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.27/1.28  tff(c_123, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_116])).
% 2.27/1.28  tff(c_128, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_123])).
% 2.27/1.28  tff(c_129, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_18, c_128])).
% 2.27/1.28  tff(c_31, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.28  tff(c_35, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_31])).
% 2.27/1.28  tff(c_36, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_35])).
% 2.27/1.28  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k6_domain_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.28  tff(c_51, plain, (![A_37, B_38]: (v4_pre_topc(k2_pre_topc(A_37, B_38), A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.28  tff(c_57, plain, (![A_37, B_7]: (v4_pre_topc(k2_pre_topc(A_37, k6_domain_1(u1_struct_0(A_37), B_7)), A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | ~m1_subset_1(B_7, u1_struct_0(A_37)) | v1_xboole_0(u1_struct_0(A_37)))), inference(resolution, [status(thm)], [c_6, c_51])).
% 2.27/1.28  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k2_pre_topc(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.28  tff(c_20, plain, (![C_31]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_31)))=k6_domain_1(u1_struct_0('#skF_2'), C_31) | ~r2_hidden(C_31, '#skF_3') | ~m1_subset_1(C_31, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.27/1.28  tff(c_150, plain, (![A_63, B_64, D_65]: (k9_subset_1(u1_struct_0(A_63), B_64, D_65)!=k6_domain_1(u1_struct_0(A_63), '#skF_1'(A_63, B_64)) | ~v4_pre_topc(D_65, A_63) | ~m1_subset_1(D_65, k1_zfmisc_1(u1_struct_0(A_63))) | v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v3_tdlat_3(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.27/1.28  tff(c_152, plain, (![C_31]: (k6_domain_1(u1_struct_0('#skF_2'), C_31)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_31)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_31)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(C_31, '#skF_3') | ~m1_subset_1(C_31, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_20, c_150])).
% 2.27/1.28  tff(c_154, plain, (![C_31]: (k6_domain_1(u1_struct_0('#skF_2'), C_31)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_31)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_31)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(C_31, '#skF_3') | ~m1_subset_1(C_31, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_152])).
% 2.27/1.28  tff(c_159, plain, (![C_72]: (k6_domain_1(u1_struct_0('#skF_2'), C_72)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_72)), '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_72)), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_72, '#skF_3') | ~m1_subset_1(C_72, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_18, c_154])).
% 2.27/1.28  tff(c_162, plain, (![C_72]: (k6_domain_1(u1_struct_0('#skF_2'), C_72)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_72)), '#skF_2') | ~r2_hidden(C_72, '#skF_3') | ~m1_subset_1(C_72, u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), C_72), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_159])).
% 2.27/1.28  tff(c_166, plain, (![C_73]: (k6_domain_1(u1_struct_0('#skF_2'), C_73)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_73)), '#skF_2') | ~r2_hidden(C_73, '#skF_3') | ~m1_subset_1(C_73, u1_struct_0('#skF_2')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), C_73), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_162])).
% 2.27/1.28  tff(c_170, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_7)), '#skF_2') | ~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_166])).
% 2.27/1.28  tff(c_174, plain, (![B_74]: (k6_domain_1(u1_struct_0('#skF_2'), B_74)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_74)), '#skF_2') | ~r2_hidden(B_74, '#skF_3') | ~m1_subset_1(B_74, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_170])).
% 2.27/1.28  tff(c_178, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_7, '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_57, c_174])).
% 2.27/1.28  tff(c_181, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_178])).
% 2.27/1.28  tff(c_182, plain, (![B_7]: (k6_domain_1(u1_struct_0('#skF_2'), B_7)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_181])).
% 2.27/1.28  tff(c_185, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(reflexivity, [status(thm), theory('equality')], [c_182])).
% 2.27/1.28  tff(c_187, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_185])).
% 2.27/1.28  tff(c_191, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_16, c_187])).
% 2.27/1.28  tff(c_194, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_191])).
% 2.27/1.28  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_18, c_194])).
% 2.27/1.28  tff(c_197, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_35])).
% 2.27/1.28  tff(c_231, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~v1_xboole_0(B_83) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.27/1.28  tff(c_241, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_231])).
% 2.27/1.28  tff(c_246, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_197, c_241])).
% 2.27/1.28  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_18, c_246])).
% 2.27/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  Inference rules
% 2.27/1.28  ----------------------
% 2.27/1.28  #Ref     : 1
% 2.27/1.28  #Sup     : 38
% 2.27/1.28  #Fact    : 0
% 2.27/1.28  #Define  : 0
% 2.27/1.28  #Split   : 2
% 2.27/1.28  #Chain   : 0
% 2.27/1.28  #Close   : 0
% 2.27/1.28  
% 2.27/1.28  Ordering : KBO
% 2.27/1.28  
% 2.27/1.28  Simplification rules
% 2.27/1.28  ----------------------
% 2.27/1.28  #Subsume      : 5
% 2.27/1.28  #Demod        : 28
% 2.27/1.29  #Tautology    : 8
% 2.27/1.29  #SimpNegUnit  : 8
% 2.27/1.29  #BackRed      : 0
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.29  Preprocessing        : 0.29
% 2.27/1.29  Parsing              : 0.16
% 2.27/1.29  CNF conversion       : 0.02
% 2.27/1.29  Main loop            : 0.23
% 2.27/1.29  Inferencing          : 0.10
% 2.27/1.29  Reduction            : 0.06
% 2.27/1.29  Demodulation         : 0.04
% 2.27/1.29  BG Simplification    : 0.01
% 2.27/1.29  Subsumption          : 0.04
% 2.27/1.29  Abstraction          : 0.01
% 2.27/1.29  MUC search           : 0.00
% 2.27/1.29  Cooper               : 0.00
% 2.27/1.29  Total                : 0.55
% 2.27/1.29  Index Insertion      : 0.00
% 2.27/1.29  Index Deletion       : 0.00
% 2.27/1.29  Index Matching       : 0.00
% 2.27/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
