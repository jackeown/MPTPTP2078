%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:37 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 222 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > r1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_borsuk_1,type,(
    r1_borsuk_1: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => r1_borsuk_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tex_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ? [C] :
              ( v1_funct_1(C)
              & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
              & v5_pre_topc(C,A,B)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
              & v3_borsuk_1(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( r1_borsuk_1(A,B)
          <=> ? [C] :
                ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
                & v3_borsuk_1(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_borsuk_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ! [A_11,B_15] :
      ( v1_funct_1('#skF_2'(A_11,B_15))
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_11,B_15] :
      ( v3_borsuk_1('#skF_2'(A_11,B_15),A_11,B_15)
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [A_11,B_15] :
      ( v5_pre_topc('#skF_2'(A_11,B_15),A_11,B_15)
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_11,B_15] :
      ( v1_funct_2('#skF_2'(A_11,B_15),u1_struct_0(A_11),u1_struct_0(B_15))
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_11,B_15] :
      ( m1_subset_1('#skF_2'(A_11,B_15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11),u1_struct_0(B_15))))
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_borsuk_1(A_38,B_39)
      | ~ v3_borsuk_1(C_40,A_38,B_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38),u1_struct_0(B_39))))
      | ~ v5_pre_topc(C_40,A_38,B_39)
      | ~ v1_funct_2(C_40,u1_struct_0(A_38),u1_struct_0(B_39))
      | ~ v1_funct_1(C_40)
      | ~ m1_pre_topc(B_39,A_38)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_41,B_42] :
      ( r1_borsuk_1(A_41,B_42)
      | ~ v3_borsuk_1('#skF_2'(A_41,B_42),A_41,B_42)
      | ~ v5_pre_topc('#skF_2'(A_41,B_42),A_41,B_42)
      | ~ v1_funct_2('#skF_2'(A_41,B_42),u1_struct_0(A_41),u1_struct_0(B_42))
      | ~ v1_funct_1('#skF_2'(A_41,B_42))
      | ~ m1_pre_topc(B_42,A_41)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | ~ v1_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_16,c_47])).

tff(c_61,plain,(
    ! [A_43,B_44] :
      ( r1_borsuk_1(A_43,B_44)
      | ~ v3_borsuk_1('#skF_2'(A_43,B_44),A_43,B_44)
      | ~ v5_pre_topc('#skF_2'(A_43,B_44),A_43,B_44)
      | ~ v1_funct_1('#skF_2'(A_43,B_44))
      | ~ m1_pre_topc(B_44,A_43)
      | v2_struct_0(B_44)
      | ~ l1_pre_topc(A_43)
      | ~ v1_tdlat_3(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_20,c_56])).

tff(c_66,plain,(
    ! [A_45,B_46] :
      ( r1_borsuk_1(A_45,B_46)
      | ~ v3_borsuk_1('#skF_2'(A_45,B_46),A_45,B_46)
      | ~ v1_funct_1('#skF_2'(A_45,B_46))
      | ~ m1_pre_topc(B_46,A_45)
      | v2_struct_0(B_46)
      | ~ l1_pre_topc(A_45)
      | ~ v1_tdlat_3(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_18,c_61])).

tff(c_71,plain,(
    ! [A_47,B_48] :
      ( r1_borsuk_1(A_47,B_48)
      | ~ v1_funct_1('#skF_2'(A_47,B_48))
      | ~ m1_pre_topc(B_48,A_47)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v1_tdlat_3(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_76,plain,(
    ! [A_49,B_50] :
      ( r1_borsuk_1(A_49,B_50)
      | ~ m1_pre_topc(B_50,A_49)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_49)
      | ~ v1_tdlat_3(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_24,plain,(
    ~ r1_borsuk_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_79,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_24])).

tff(c_82,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_26,c_79])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_28,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.22  
% 2.19/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.22  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > r1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.24/1.22  
% 2.24/1.22  %Foreground sorts:
% 2.24/1.22  
% 2.24/1.22  
% 2.24/1.22  %Background operators:
% 2.24/1.22  
% 2.24/1.22  
% 2.24/1.22  %Foreground operators:
% 2.24/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.24/1.22  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.24/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.22  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.24/1.22  tff(r1_borsuk_1, type, r1_borsuk_1: ($i * $i) > $o).
% 2.24/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.22  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.24/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.24/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.22  
% 2.24/1.25  tff(f_95, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => r1_borsuk_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tex_2)).
% 2.24/1.25  tff(f_77, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (?[C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & v3_borsuk_1(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tex_2)).
% 2.24/1.25  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (r1_borsuk_1(A, B) <=> (?[C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & v3_borsuk_1(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_borsuk_1)).
% 2.24/1.25  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_28, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_32, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_22, plain, (![A_11, B_15]: (v1_funct_1('#skF_2'(A_11, B_15)) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v1_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.25  tff(c_14, plain, (![A_11, B_15]: (v3_borsuk_1('#skF_2'(A_11, B_15), A_11, B_15) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v1_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.25  tff(c_18, plain, (![A_11, B_15]: (v5_pre_topc('#skF_2'(A_11, B_15), A_11, B_15) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v1_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.25  tff(c_20, plain, (![A_11, B_15]: (v1_funct_2('#skF_2'(A_11, B_15), u1_struct_0(A_11), u1_struct_0(B_15)) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v1_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.25  tff(c_16, plain, (![A_11, B_15]: (m1_subset_1('#skF_2'(A_11, B_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11), u1_struct_0(B_15)))) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v1_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.25  tff(c_47, plain, (![A_38, B_39, C_40]: (r1_borsuk_1(A_38, B_39) | ~v3_borsuk_1(C_40, A_38, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(B_39)))) | ~v5_pre_topc(C_40, A_38, B_39) | ~v1_funct_2(C_40, u1_struct_0(A_38), u1_struct_0(B_39)) | ~v1_funct_1(C_40) | ~m1_pre_topc(B_39, A_38) | v2_struct_0(B_39) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.25  tff(c_56, plain, (![A_41, B_42]: (r1_borsuk_1(A_41, B_42) | ~v3_borsuk_1('#skF_2'(A_41, B_42), A_41, B_42) | ~v5_pre_topc('#skF_2'(A_41, B_42), A_41, B_42) | ~v1_funct_2('#skF_2'(A_41, B_42), u1_struct_0(A_41), u1_struct_0(B_42)) | ~v1_funct_1('#skF_2'(A_41, B_42)) | ~m1_pre_topc(B_42, A_41) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | ~v1_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_16, c_47])).
% 2.24/1.25  tff(c_61, plain, (![A_43, B_44]: (r1_borsuk_1(A_43, B_44) | ~v3_borsuk_1('#skF_2'(A_43, B_44), A_43, B_44) | ~v5_pre_topc('#skF_2'(A_43, B_44), A_43, B_44) | ~v1_funct_1('#skF_2'(A_43, B_44)) | ~m1_pre_topc(B_44, A_43) | v2_struct_0(B_44) | ~l1_pre_topc(A_43) | ~v1_tdlat_3(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(resolution, [status(thm)], [c_20, c_56])).
% 2.24/1.25  tff(c_66, plain, (![A_45, B_46]: (r1_borsuk_1(A_45, B_46) | ~v3_borsuk_1('#skF_2'(A_45, B_46), A_45, B_46) | ~v1_funct_1('#skF_2'(A_45, B_46)) | ~m1_pre_topc(B_46, A_45) | v2_struct_0(B_46) | ~l1_pre_topc(A_45) | ~v1_tdlat_3(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_18, c_61])).
% 2.24/1.25  tff(c_71, plain, (![A_47, B_48]: (r1_borsuk_1(A_47, B_48) | ~v1_funct_1('#skF_2'(A_47, B_48)) | ~m1_pre_topc(B_48, A_47) | v2_struct_0(B_48) | ~l1_pre_topc(A_47) | ~v1_tdlat_3(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_14, c_66])).
% 2.24/1.25  tff(c_76, plain, (![A_49, B_50]: (r1_borsuk_1(A_49, B_50) | ~m1_pre_topc(B_50, A_49) | v2_struct_0(B_50) | ~l1_pre_topc(A_49) | ~v1_tdlat_3(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_22, c_71])).
% 2.24/1.25  tff(c_24, plain, (~r1_borsuk_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.24/1.25  tff(c_79, plain, (~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_24])).
% 2.24/1.25  tff(c_82, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_26, c_79])).
% 2.24/1.25  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_28, c_82])).
% 2.24/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.25  
% 2.24/1.25  Inference rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Ref     : 0
% 2.24/1.25  #Sup     : 7
% 2.24/1.25  #Fact    : 0
% 2.24/1.25  #Define  : 0
% 2.24/1.25  #Split   : 0
% 2.24/1.25  #Chain   : 0
% 2.24/1.25  #Close   : 0
% 2.24/1.25  
% 2.24/1.25  Ordering : KBO
% 2.24/1.25  
% 2.24/1.25  Simplification rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Subsume      : 4
% 2.24/1.25  #Demod        : 4
% 2.24/1.25  #Tautology    : 1
% 2.24/1.25  #SimpNegUnit  : 1
% 2.24/1.25  #BackRed      : 0
% 2.24/1.25  
% 2.24/1.25  #Partial instantiations: 0
% 2.24/1.25  #Strategies tried      : 1
% 2.24/1.25  
% 2.24/1.25  Timing (in seconds)
% 2.24/1.25  ----------------------
% 2.24/1.25  Preprocessing        : 0.28
% 2.24/1.26  Parsing              : 0.15
% 2.24/1.26  CNF conversion       : 0.02
% 2.24/1.26  Main loop            : 0.18
% 2.24/1.26  Inferencing          : 0.09
% 2.24/1.26  Reduction            : 0.05
% 2.24/1.26  Demodulation         : 0.03
% 2.24/1.26  BG Simplification    : 0.01
% 2.24/1.26  Subsumption          : 0.03
% 2.24/1.26  Abstraction          : 0.01
% 2.24/1.26  MUC search           : 0.00
% 2.24/1.26  Cooper               : 0.00
% 2.24/1.26  Total                : 0.51
% 2.24/1.26  Index Insertion      : 0.00
% 2.24/1.26  Index Deletion       : 0.00
% 2.24/1.26  Index Matching       : 0.00
% 2.24/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
