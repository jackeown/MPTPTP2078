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
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 118 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 339 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_4] : r1_xboole_0(k1_xboole_0,A_4) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

tff(c_49,plain,(
    ! [B_29,A_30] :
      ( ~ r1_xboole_0(B_29,A_30)
      | ~ r1_tarski(B_29,A_30)
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [A_4] :
      ( ~ r1_tarski(k1_xboole_0,A_4)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_37,c_49])).

tff(c_58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [B_35,A_36] :
      ( v2_tex_2(B_35,A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ v1_xboole_0(B_35)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_75,plain,(
    ! [A_36] :
      ( v2_tex_2(k1_xboole_0,A_36)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_78,plain,(
    ! [A_36] :
      ( v2_tex_2(k1_xboole_0,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_75])).

tff(c_93,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1('#skF_1'(A_45,B_46),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v2_tex_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v3_tdlat_3(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    ! [B_21] :
      ( ~ v3_tex_2(B_21,'#skF_2')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_106,plain,(
    ! [B_46] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_46),'#skF_2')
      | ~ v2_tex_2(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_93,c_22])).

tff(c_113,plain,(
    ! [B_46] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_46),'#skF_2')
      | ~ v2_tex_2(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_106])).

tff(c_115,plain,(
    ! [B_47] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_47),'#skF_2')
      | ~ v2_tex_2(B_47,'#skF_2')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_113])).

tff(c_128,plain,
    ( ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_129,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_132,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_135])).

tff(c_139,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_87,plain,(
    ! [A_42,B_43] :
      ( v3_tex_2('#skF_1'(A_42,B_43),A_42)
      | ~ v2_tex_2(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v3_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91,plain,(
    ! [A_42] :
      ( v3_tex_2('#skF_1'(A_42,k1_xboole_0),A_42)
      | ~ v2_tex_2(k1_xboole_0,A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v3_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_138,plain,(
    ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_150,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_91,c_138])).

tff(c_153,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_139,c_150])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n004.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 18:03:08 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.15  
% 2.12/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.15  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.12/1.15  
% 2.12/1.15  %Foreground sorts:
% 2.12/1.15  
% 2.12/1.15  
% 2.12/1.15  %Background operators:
% 2.12/1.15  
% 2.12/1.15  
% 2.12/1.15  %Foreground operators:
% 2.12/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.12/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.12/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.15  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.12/1.15  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.12/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.15  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.15  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.12/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.12/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.12/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.15  
% 2.12/1.16  tff(f_101, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.12/1.16  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.16  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.12/1.16  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.12/1.16  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.12/1.16  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.12/1.16  tff(f_86, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.12/1.16  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.12/1.16  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.12/1.16  tff(c_26, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.12/1.16  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.12/1.16  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.16  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.16  tff(c_34, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.16  tff(c_37, plain, (![A_4]: (r1_xboole_0(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_6, c_34])).
% 2.12/1.16  tff(c_49, plain, (![B_29, A_30]: (~r1_xboole_0(B_29, A_30) | ~r1_tarski(B_29, A_30) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.16  tff(c_52, plain, (![A_4]: (~r1_tarski(k1_xboole_0, A_4) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_37, c_49])).
% 2.12/1.16  tff(c_58, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_52])).
% 2.12/1.16  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.16  tff(c_71, plain, (![B_35, A_36]: (v2_tex_2(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~v1_xboole_0(B_35) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.16  tff(c_75, plain, (![A_36]: (v2_tex_2(k1_xboole_0, A_36) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(resolution, [status(thm)], [c_10, c_71])).
% 2.12/1.16  tff(c_78, plain, (![A_36]: (v2_tex_2(k1_xboole_0, A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_75])).
% 2.12/1.16  tff(c_93, plain, (![A_45, B_46]: (m1_subset_1('#skF_1'(A_45, B_46), k1_zfmisc_1(u1_struct_0(A_45))) | ~v2_tex_2(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v3_tdlat_3(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.12/1.16  tff(c_22, plain, (![B_21]: (~v3_tex_2(B_21, '#skF_2') | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.12/1.16  tff(c_106, plain, (![B_46]: (~v3_tex_2('#skF_1'('#skF_2', B_46), '#skF_2') | ~v2_tex_2(B_46, '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_22])).
% 2.12/1.16  tff(c_113, plain, (![B_46]: (~v3_tex_2('#skF_1'('#skF_2', B_46), '#skF_2') | ~v2_tex_2(B_46, '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_106])).
% 2.12/1.16  tff(c_115, plain, (![B_47]: (~v3_tex_2('#skF_1'('#skF_2', B_47), '#skF_2') | ~v2_tex_2(B_47, '#skF_2') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_113])).
% 2.12/1.16  tff(c_128, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_10, c_115])).
% 2.12/1.16  tff(c_129, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_128])).
% 2.12/1.16  tff(c_132, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_129])).
% 2.12/1.16  tff(c_135, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_132])).
% 2.12/1.16  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_135])).
% 2.12/1.16  tff(c_139, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_128])).
% 2.12/1.16  tff(c_87, plain, (![A_42, B_43]: (v3_tex_2('#skF_1'(A_42, B_43), A_42) | ~v2_tex_2(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v3_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.12/1.16  tff(c_91, plain, (![A_42]: (v3_tex_2('#skF_1'(A_42, k1_xboole_0), A_42) | ~v2_tex_2(k1_xboole_0, A_42) | ~l1_pre_topc(A_42) | ~v3_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(resolution, [status(thm)], [c_10, c_87])).
% 2.12/1.16  tff(c_138, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2')), inference(splitRight, [status(thm)], [c_128])).
% 2.12/1.16  tff(c_150, plain, (~v2_tex_2(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_91, c_138])).
% 2.12/1.16  tff(c_153, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_139, c_150])).
% 2.12/1.16  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_153])).
% 2.12/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.16  
% 2.12/1.16  Inference rules
% 2.12/1.16  ----------------------
% 2.12/1.16  #Ref     : 0
% 2.12/1.16  #Sup     : 21
% 2.12/1.16  #Fact    : 0
% 2.12/1.16  #Define  : 0
% 2.12/1.16  #Split   : 1
% 2.12/1.16  #Chain   : 0
% 2.12/1.16  #Close   : 0
% 2.12/1.16  
% 2.12/1.16  Ordering : KBO
% 2.12/1.16  
% 2.12/1.16  Simplification rules
% 2.12/1.16  ----------------------
% 2.12/1.16  #Subsume      : 0
% 2.12/1.16  #Demod        : 17
% 2.12/1.16  #Tautology    : 3
% 2.12/1.16  #SimpNegUnit  : 4
% 2.12/1.16  #BackRed      : 0
% 2.12/1.16  
% 2.12/1.16  #Partial instantiations: 0
% 2.12/1.16  #Strategies tried      : 1
% 2.12/1.16  
% 2.12/1.16  Timing (in seconds)
% 2.12/1.16  ----------------------
% 2.12/1.16  Preprocessing        : 0.28
% 2.12/1.16  Parsing              : 0.16
% 2.12/1.17  CNF conversion       : 0.02
% 2.12/1.17  Main loop            : 0.17
% 2.12/1.17  Inferencing          : 0.07
% 2.12/1.17  Reduction            : 0.04
% 2.12/1.17  Demodulation         : 0.03
% 2.12/1.17  BG Simplification    : 0.01
% 2.12/1.17  Subsumption          : 0.03
% 2.12/1.17  Abstraction          : 0.01
% 2.12/1.17  MUC search           : 0.00
% 2.12/1.17  Cooper               : 0.00
% 2.12/1.17  Total                : 0.48
% 2.12/1.17  Index Insertion      : 0.00
% 2.12/1.17  Index Deletion       : 0.00
% 2.12/1.17  Index Matching       : 0.00
% 2.12/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
