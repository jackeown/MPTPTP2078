%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 115 expanded)
%              Number of leaves         :   26 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 334 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_83,axiom,(
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
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_29] :
      ( v1_xboole_0(A_29)
      | r2_hidden('#skF_1'(A_29),A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [A_31] :
      ( ~ r1_tarski(A_31,'#skF_1'(A_31))
      | v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_35,c_12])).

tff(c_55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [B_37,A_38] :
      ( v2_tex_2(B_37,A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ v1_xboole_0(B_37)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    ! [A_38] :
      ( v2_tex_2(k1_xboole_0,A_38)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_73,plain,(
    ! [A_38] :
      ( v2_tex_2(k1_xboole_0,A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_70])).

tff(c_86,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1('#skF_2'(A_44,B_45),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ v2_tex_2(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v3_tdlat_3(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [B_22] :
      ( ~ v3_tex_2(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_99,plain,(
    ! [B_45] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_45),'#skF_3')
      | ~ v2_tex_2(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_86,c_22])).

tff(c_106,plain,(
    ! [B_45] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_45),'#skF_3')
      | ~ v2_tex_2(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_99])).

tff(c_108,plain,(
    ! [B_46] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_46),'#skF_3')
      | ~ v2_tex_2(B_46,'#skF_3')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_106])).

tff(c_121,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',k1_xboole_0),'#skF_3')
    | ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_122,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_125,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_122])).

tff(c_128,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_125])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_128])).

tff(c_132,plain,(
    v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_81,plain,(
    ! [A_42,B_43] :
      ( v3_tex_2('#skF_2'(A_42,B_43),A_42)
      | ~ v2_tex_2(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v3_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,(
    ! [A_47] :
      ( v3_tex_2('#skF_2'(A_47,k1_xboole_0),A_47)
      | ~ v2_tex_2(k1_xboole_0,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v3_tdlat_3(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_131,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3',k1_xboole_0),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_136,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_131])).

tff(c_139,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_132,c_136])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:37:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.18  
% 1.94/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.19  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.94/1.19  
% 1.94/1.19  %Foreground sorts:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Background operators:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Foreground operators:
% 1.94/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.94/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.19  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.94/1.19  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.94/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.19  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.94/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.19  
% 1.94/1.20  tff(f_98, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 1.94/1.20  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.94/1.20  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.94/1.20  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.94/1.20  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 1.94/1.20  tff(f_83, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 1.94/1.20  tff(c_30, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 1.94/1.20  tff(c_28, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 1.94/1.20  tff(c_26, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 1.94/1.20  tff(c_24, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 1.94/1.20  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.20  tff(c_35, plain, (![A_29]: (v1_xboole_0(A_29) | r2_hidden('#skF_1'(A_29), A_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.20  tff(c_12, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.20  tff(c_50, plain, (![A_31]: (~r1_tarski(A_31, '#skF_1'(A_31)) | v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_35, c_12])).
% 1.94/1.20  tff(c_55, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_50])).
% 1.94/1.20  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.20  tff(c_66, plain, (![B_37, A_38]: (v2_tex_2(B_37, A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_38))) | ~v1_xboole_0(B_37) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.20  tff(c_70, plain, (![A_38]: (v2_tex_2(k1_xboole_0, A_38) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_8, c_66])).
% 1.94/1.20  tff(c_73, plain, (![A_38]: (v2_tex_2(k1_xboole_0, A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_70])).
% 1.94/1.20  tff(c_86, plain, (![A_44, B_45]: (m1_subset_1('#skF_2'(A_44, B_45), k1_zfmisc_1(u1_struct_0(A_44))) | ~v2_tex_2(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v3_tdlat_3(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.94/1.20  tff(c_22, plain, (![B_22]: (~v3_tex_2(B_22, '#skF_3') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 1.94/1.20  tff(c_99, plain, (![B_45]: (~v3_tex_2('#skF_2'('#skF_3', B_45), '#skF_3') | ~v2_tex_2(B_45, '#skF_3') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_22])).
% 1.94/1.20  tff(c_106, plain, (![B_45]: (~v3_tex_2('#skF_2'('#skF_3', B_45), '#skF_3') | ~v2_tex_2(B_45, '#skF_3') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_99])).
% 1.94/1.20  tff(c_108, plain, (![B_46]: (~v3_tex_2('#skF_2'('#skF_3', B_46), '#skF_3') | ~v2_tex_2(B_46, '#skF_3') | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_106])).
% 1.94/1.20  tff(c_121, plain, (~v3_tex_2('#skF_2'('#skF_3', k1_xboole_0), '#skF_3') | ~v2_tex_2(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_8, c_108])).
% 1.94/1.20  tff(c_122, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_121])).
% 1.94/1.20  tff(c_125, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_73, c_122])).
% 1.94/1.20  tff(c_128, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_125])).
% 1.94/1.20  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_128])).
% 1.94/1.20  tff(c_132, plain, (v2_tex_2(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_121])).
% 1.94/1.20  tff(c_81, plain, (![A_42, B_43]: (v3_tex_2('#skF_2'(A_42, B_43), A_42) | ~v2_tex_2(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v3_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.94/1.20  tff(c_133, plain, (![A_47]: (v3_tex_2('#skF_2'(A_47, k1_xboole_0), A_47) | ~v2_tex_2(k1_xboole_0, A_47) | ~l1_pre_topc(A_47) | ~v3_tdlat_3(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_8, c_81])).
% 1.94/1.20  tff(c_131, plain, (~v3_tex_2('#skF_2'('#skF_3', k1_xboole_0), '#skF_3')), inference(splitRight, [status(thm)], [c_121])).
% 1.94/1.20  tff(c_136, plain, (~v2_tex_2(k1_xboole_0, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_131])).
% 1.94/1.20  tff(c_139, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_132, c_136])).
% 1.94/1.20  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_139])).
% 1.94/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  Inference rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Ref     : 0
% 1.94/1.20  #Sup     : 18
% 1.94/1.20  #Fact    : 0
% 1.94/1.20  #Define  : 0
% 1.94/1.20  #Split   : 1
% 1.94/1.20  #Chain   : 0
% 1.94/1.20  #Close   : 0
% 1.94/1.20  
% 1.94/1.20  Ordering : KBO
% 1.94/1.20  
% 1.94/1.20  Simplification rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Subsume      : 0
% 1.94/1.20  #Demod        : 15
% 1.94/1.20  #Tautology    : 3
% 1.94/1.20  #SimpNegUnit  : 4
% 1.94/1.20  #BackRed      : 0
% 1.94/1.20  
% 1.94/1.20  #Partial instantiations: 0
% 1.94/1.20  #Strategies tried      : 1
% 1.94/1.20  
% 1.94/1.20  Timing (in seconds)
% 1.94/1.20  ----------------------
% 1.94/1.20  Preprocessing        : 0.28
% 1.94/1.20  Parsing              : 0.16
% 1.94/1.20  CNF conversion       : 0.02
% 1.94/1.20  Main loop            : 0.16
% 1.94/1.20  Inferencing          : 0.07
% 1.94/1.20  Reduction            : 0.04
% 1.94/1.20  Demodulation         : 0.03
% 1.94/1.20  BG Simplification    : 0.01
% 1.94/1.20  Subsumption          : 0.03
% 1.94/1.20  Abstraction          : 0.01
% 1.94/1.20  MUC search           : 0.00
% 1.94/1.20  Cooper               : 0.00
% 1.94/1.20  Total                : 0.47
% 1.94/1.20  Index Insertion      : 0.00
% 1.94/1.20  Index Deletion       : 0.00
% 1.94/1.20  Index Matching       : 0.00
% 1.94/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
