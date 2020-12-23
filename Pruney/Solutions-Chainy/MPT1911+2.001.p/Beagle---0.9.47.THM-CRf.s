%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 254 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > r1_borsuk_1 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & m1_pre_topc(B,A) )
           => r1_borsuk_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v1_tdlat_3(B)
            & m1_pre_topc(B,A) )
         => ? [C] :
              ( v1_funct_1(C)
              & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
              & v5_pre_topc(C,A,B)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
              & v3_borsuk_1(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tex_2)).

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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_22,plain,(
    ! [A_11,B_15] :
      ( v1_funct_1('#skF_2'(A_11,B_15))
      | ~ m1_pre_topc(B_15,A_11)
      | ~ v1_tdlat_3(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v3_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_11,B_15] :
      ( v3_borsuk_1('#skF_2'(A_11,B_15),A_11,B_15)
      | ~ m1_pre_topc(B_15,A_11)
      | ~ v1_tdlat_3(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v3_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_11,B_15] :
      ( v5_pre_topc('#skF_2'(A_11,B_15),A_11,B_15)
      | ~ m1_pre_topc(B_15,A_11)
      | ~ v1_tdlat_3(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v3_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_11,B_15] :
      ( v1_funct_2('#skF_2'(A_11,B_15),u1_struct_0(A_11),u1_struct_0(B_15))
      | ~ m1_pre_topc(B_15,A_11)
      | ~ v1_tdlat_3(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v3_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_11,B_15] :
      ( m1_subset_1('#skF_2'(A_11,B_15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11),u1_struct_0(B_15))))
      | ~ m1_pre_topc(B_15,A_11)
      | ~ v1_tdlat_3(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v3_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
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

tff(c_58,plain,(
    ! [A_41,B_42] :
      ( r1_borsuk_1(A_41,B_42)
      | ~ v3_borsuk_1('#skF_2'(A_41,B_42),A_41,B_42)
      | ~ v5_pre_topc('#skF_2'(A_41,B_42),A_41,B_42)
      | ~ v1_funct_2('#skF_2'(A_41,B_42),u1_struct_0(A_41),u1_struct_0(B_42))
      | ~ v1_funct_1('#skF_2'(A_41,B_42))
      | ~ m1_pre_topc(B_42,A_41)
      | ~ v1_tdlat_3(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | ~ v3_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_63,plain,(
    ! [A_43,B_44] :
      ( r1_borsuk_1(A_43,B_44)
      | ~ v3_borsuk_1('#skF_2'(A_43,B_44),A_43,B_44)
      | ~ v5_pre_topc('#skF_2'(A_43,B_44),A_43,B_44)
      | ~ v1_funct_1('#skF_2'(A_43,B_44))
      | ~ m1_pre_topc(B_44,A_43)
      | ~ v1_tdlat_3(B_44)
      | v2_struct_0(B_44)
      | ~ l1_pre_topc(A_43)
      | ~ v3_tdlat_3(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_20,c_58])).

tff(c_68,plain,(
    ! [A_45,B_46] :
      ( r1_borsuk_1(A_45,B_46)
      | ~ v3_borsuk_1('#skF_2'(A_45,B_46),A_45,B_46)
      | ~ v1_funct_1('#skF_2'(A_45,B_46))
      | ~ m1_pre_topc(B_46,A_45)
      | ~ v1_tdlat_3(B_46)
      | v2_struct_0(B_46)
      | ~ l1_pre_topc(A_45)
      | ~ v3_tdlat_3(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_73,plain,(
    ! [A_47,B_48] :
      ( r1_borsuk_1(A_47,B_48)
      | ~ v1_funct_1('#skF_2'(A_47,B_48))
      | ~ m1_pre_topc(B_48,A_47)
      | ~ v1_tdlat_3(B_48)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v3_tdlat_3(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_78,plain,(
    ! [A_49,B_50] :
      ( r1_borsuk_1(A_49,B_50)
      | ~ m1_pre_topc(B_50,A_49)
      | ~ v1_tdlat_3(B_50)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_49)
      | ~ v3_tdlat_3(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_24,plain,(
    ~ r1_borsuk_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_81,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_24])).

tff(c_84,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_28,c_26,c_81])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:02:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  
% 2.32/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > r1_borsuk_1 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.32/1.26  
% 2.32/1.26  %Foreground sorts:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Background operators:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Foreground operators:
% 2.32/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.26  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.32/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.26  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.32/1.26  tff(r1_borsuk_1, type, r1_borsuk_1: ($i * $i) > $o).
% 2.32/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.26  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.32/1.26  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.32/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.32/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.26  
% 2.32/1.27  tff(f_99, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v1_tdlat_3(B)) & m1_pre_topc(B, A)) => r1_borsuk_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tex_2)).
% 2.32/1.27  tff(f_79, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v1_tdlat_3(B)) & m1_pre_topc(B, A)) => (?[C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & v3_borsuk_1(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tex_2)).
% 2.32/1.27  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (r1_borsuk_1(A, B) <=> (?[C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & v3_borsuk_1(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_borsuk_1)).
% 2.32/1.27  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_30, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_36, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_34, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_28, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_22, plain, (![A_11, B_15]: (v1_funct_1('#skF_2'(A_11, B_15)) | ~m1_pre_topc(B_15, A_11) | ~v1_tdlat_3(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v3_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.32/1.27  tff(c_14, plain, (![A_11, B_15]: (v3_borsuk_1('#skF_2'(A_11, B_15), A_11, B_15) | ~m1_pre_topc(B_15, A_11) | ~v1_tdlat_3(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v3_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.32/1.27  tff(c_18, plain, (![A_11, B_15]: (v5_pre_topc('#skF_2'(A_11, B_15), A_11, B_15) | ~m1_pre_topc(B_15, A_11) | ~v1_tdlat_3(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v3_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.32/1.27  tff(c_20, plain, (![A_11, B_15]: (v1_funct_2('#skF_2'(A_11, B_15), u1_struct_0(A_11), u1_struct_0(B_15)) | ~m1_pre_topc(B_15, A_11) | ~v1_tdlat_3(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v3_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.32/1.27  tff(c_16, plain, (![A_11, B_15]: (m1_subset_1('#skF_2'(A_11, B_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11), u1_struct_0(B_15)))) | ~m1_pre_topc(B_15, A_11) | ~v1_tdlat_3(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v3_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.32/1.27  tff(c_49, plain, (![A_38, B_39, C_40]: (r1_borsuk_1(A_38, B_39) | ~v3_borsuk_1(C_40, A_38, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_38), u1_struct_0(B_39)))) | ~v5_pre_topc(C_40, A_38, B_39) | ~v1_funct_2(C_40, u1_struct_0(A_38), u1_struct_0(B_39)) | ~v1_funct_1(C_40) | ~m1_pre_topc(B_39, A_38) | v2_struct_0(B_39) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.27  tff(c_58, plain, (![A_41, B_42]: (r1_borsuk_1(A_41, B_42) | ~v3_borsuk_1('#skF_2'(A_41, B_42), A_41, B_42) | ~v5_pre_topc('#skF_2'(A_41, B_42), A_41, B_42) | ~v1_funct_2('#skF_2'(A_41, B_42), u1_struct_0(A_41), u1_struct_0(B_42)) | ~v1_funct_1('#skF_2'(A_41, B_42)) | ~m1_pre_topc(B_42, A_41) | ~v1_tdlat_3(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | ~v3_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_16, c_49])).
% 2.32/1.27  tff(c_63, plain, (![A_43, B_44]: (r1_borsuk_1(A_43, B_44) | ~v3_borsuk_1('#skF_2'(A_43, B_44), A_43, B_44) | ~v5_pre_topc('#skF_2'(A_43, B_44), A_43, B_44) | ~v1_funct_1('#skF_2'(A_43, B_44)) | ~m1_pre_topc(B_44, A_43) | ~v1_tdlat_3(B_44) | v2_struct_0(B_44) | ~l1_pre_topc(A_43) | ~v3_tdlat_3(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(resolution, [status(thm)], [c_20, c_58])).
% 2.32/1.27  tff(c_68, plain, (![A_45, B_46]: (r1_borsuk_1(A_45, B_46) | ~v3_borsuk_1('#skF_2'(A_45, B_46), A_45, B_46) | ~v1_funct_1('#skF_2'(A_45, B_46)) | ~m1_pre_topc(B_46, A_45) | ~v1_tdlat_3(B_46) | v2_struct_0(B_46) | ~l1_pre_topc(A_45) | ~v3_tdlat_3(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.32/1.27  tff(c_73, plain, (![A_47, B_48]: (r1_borsuk_1(A_47, B_48) | ~v1_funct_1('#skF_2'(A_47, B_48)) | ~m1_pre_topc(B_48, A_47) | ~v1_tdlat_3(B_48) | v2_struct_0(B_48) | ~l1_pre_topc(A_47) | ~v3_tdlat_3(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_14, c_68])).
% 2.32/1.27  tff(c_78, plain, (![A_49, B_50]: (r1_borsuk_1(A_49, B_50) | ~m1_pre_topc(B_50, A_49) | ~v1_tdlat_3(B_50) | v2_struct_0(B_50) | ~l1_pre_topc(A_49) | ~v3_tdlat_3(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.32/1.27  tff(c_24, plain, (~r1_borsuk_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.32/1.27  tff(c_81, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~v1_tdlat_3('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_24])).
% 2.32/1.27  tff(c_84, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_28, c_26, c_81])).
% 2.32/1.27  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_84])).
% 2.32/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.27  
% 2.32/1.27  Inference rules
% 2.32/1.27  ----------------------
% 2.32/1.27  #Ref     : 0
% 2.32/1.27  #Sup     : 7
% 2.32/1.27  #Fact    : 0
% 2.32/1.27  #Define  : 0
% 2.32/1.27  #Split   : 0
% 2.32/1.27  #Chain   : 0
% 2.32/1.27  #Close   : 0
% 2.32/1.27  
% 2.32/1.27  Ordering : KBO
% 2.32/1.27  
% 2.32/1.27  Simplification rules
% 2.32/1.27  ----------------------
% 2.32/1.27  #Subsume      : 4
% 2.32/1.27  #Demod        : 5
% 2.32/1.27  #Tautology    : 1
% 2.32/1.27  #SimpNegUnit  : 1
% 2.32/1.27  #BackRed      : 0
% 2.32/1.27  
% 2.32/1.27  #Partial instantiations: 0
% 2.32/1.27  #Strategies tried      : 1
% 2.32/1.27  
% 2.32/1.27  Timing (in seconds)
% 2.32/1.27  ----------------------
% 2.32/1.28  Preprocessing        : 0.30
% 2.32/1.28  Parsing              : 0.17
% 2.32/1.28  CNF conversion       : 0.02
% 2.32/1.28  Main loop            : 0.16
% 2.32/1.28  Inferencing          : 0.08
% 2.32/1.28  Reduction            : 0.04
% 2.32/1.28  Demodulation         : 0.03
% 2.32/1.28  BG Simplification    : 0.01
% 2.32/1.28  Subsumption          : 0.02
% 2.32/1.28  Abstraction          : 0.01
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.49
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
