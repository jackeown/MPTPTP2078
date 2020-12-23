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
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 178 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 ( 530 expanded)
%              Number of equality atoms :   41 (  91 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_tmap_1 > k5_tmap_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != k6_tmap_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_98,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_137,plain,(
    ! [B_51,A_52] :
      ( v3_pre_topc(B_51,A_52)
      | ~ r2_hidden(B_51,u1_pre_topc(A_52))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_151,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_143])).

tff(c_152,plain,(
    ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_151])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_699,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,u1_pre_topc(A_92))
      | k5_tmap_1(A_92,B_91) != u1_pre_topc(A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_711,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | k5_tmap_1('#skF_4','#skF_5') != u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_699])).

tff(c_720,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | k5_tmap_1('#skF_4','#skF_5') != u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_711])).

tff(c_721,plain,(
    k5_tmap_1('#skF_4','#skF_5') != u1_pre_topc('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_152,c_720])).

tff(c_270,plain,(
    ! [A_62,B_63] :
      ( u1_pre_topc(k6_tmap_1(A_62,B_63)) = k5_tmap_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_282,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_270])).

tff(c_290,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_282])).

tff(c_291,plain,(
    u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_290])).

tff(c_42,plain,(
    ! [A_6] :
      ( r2_hidden(u1_struct_0(A_6),u1_pre_topc(A_6))
      | ~ v2_pre_topc(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [A_23] :
      ( m1_subset_1(u1_pre_topc(A_23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23))))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_88,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_38,A_23] :
      ( m1_subset_1(A_38,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ r2_hidden(A_38,u1_pre_topc(A_23))
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_546,plain,(
    ! [A_81,B_82] :
      ( k5_tmap_1(A_81,B_82) = u1_pre_topc(A_81)
      | ~ r2_hidden(B_82,u1_pre_topc(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_593,plain,(
    ! [A_85,A_86] :
      ( k5_tmap_1(A_85,A_86) = u1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | ~ r2_hidden(A_86,u1_pre_topc(A_85))
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_95,c_546])).

tff(c_616,plain,(
    ! [A_6] :
      ( k5_tmap_1(A_6,u1_struct_0(A_6)) = u1_pre_topc(A_6)
      | v2_struct_0(A_6)
      | ~ v2_pre_topc(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_42,c_593])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_570,plain,(
    ! [A_83,B_84] :
      ( g1_pre_topc(u1_struct_0(A_83),k5_tmap_1(A_83,B_84)) = k6_tmap_1(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_633,plain,(
    ! [A_88] :
      ( g1_pre_topc(u1_struct_0(A_88),k5_tmap_1(A_88,u1_struct_0(A_88))) = k6_tmap_1(A_88,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_75,c_570])).

tff(c_945,plain,(
    ! [A_107] :
      ( g1_pre_topc(u1_struct_0(A_107),u1_pre_topc(A_107)) = k6_tmap_1(A_107,u1_struct_0(A_107))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107)
      | v2_struct_0(A_107)
      | ~ v2_pre_topc(A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_633])).

tff(c_74,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_106,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_74])).

tff(c_951,plain,
    ( k6_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_106])).

tff(c_972,plain,
    ( k6_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_64,c_62,c_951])).

tff(c_973,plain,(
    k6_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_972])).

tff(c_292,plain,(
    ! [A_62] :
      ( u1_pre_topc(k6_tmap_1(A_62,u1_struct_0(A_62))) = k5_tmap_1(A_62,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_75,c_270])).

tff(c_986,plain,
    ( k5_tmap_1('#skF_4',u1_struct_0('#skF_4')) = u1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_292])).

tff(c_996,plain,
    ( k5_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k5_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_291,c_986])).

tff(c_997,plain,(
    k5_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k5_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_996])).

tff(c_1012,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_616])).

tff(c_1025,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_1012])).

tff(c_1027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_721,c_1025])).

tff(c_1028,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != k6_tmap_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1029,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1069,plain,(
    ! [B_122,A_123] :
      ( r2_hidden(B_122,u1_pre_topc(A_123))
      | ~ v3_pre_topc(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1075,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1069])).

tff(c_1083,plain,(
    r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1029,c_1075])).

tff(c_1532,plain,(
    ! [A_150,B_151] :
      ( k5_tmap_1(A_150,B_151) = u1_pre_topc(A_150)
      | ~ r2_hidden(B_151,u1_pre_topc(A_150))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1547,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1532])).

tff(c_1557,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1083,c_1547])).

tff(c_1558,plain,(
    k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1557])).

tff(c_1719,plain,(
    ! [A_156,B_157] :
      ( g1_pre_topc(u1_struct_0(A_156),k5_tmap_1(A_156,B_157)) = k6_tmap_1(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1731,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1719])).

tff(c_1741,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1558,c_1731])).

tff(c_1743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1028,c_1741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:18:38 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.61  
% 3.86/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.62  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_tmap_1 > k5_tmap_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3
% 3.86/1.62  
% 3.86/1.62  %Foreground sorts:
% 3.86/1.62  
% 3.86/1.62  
% 3.86/1.62  %Background operators:
% 3.86/1.62  
% 3.86/1.62  
% 3.86/1.62  %Foreground operators:
% 3.86/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.86/1.62  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.86/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.86/1.62  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.86/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.62  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.86/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.86/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.62  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.86/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.62  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.86/1.62  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.86/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.86/1.62  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.86/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.86/1.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.86/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.62  
% 3.86/1.63  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.86/1.63  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.86/1.63  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.86/1.63  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.86/1.63  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.86/1.63  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.86/1.63  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.86/1.63  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.86/1.63  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.86/1.63  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.86/1.63  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.63  tff(c_68, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=k6_tmap_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.63  tff(c_98, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.86/1.63  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.63  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.63  tff(c_137, plain, (![B_51, A_52]: (v3_pre_topc(B_51, A_52) | ~r2_hidden(B_51, u1_pre_topc(A_52)) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.86/1.63  tff(c_143, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_137])).
% 3.86/1.63  tff(c_151, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_143])).
% 3.86/1.63  tff(c_152, plain, (~r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_98, c_151])).
% 3.86/1.63  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.63  tff(c_699, plain, (![B_91, A_92]: (r2_hidden(B_91, u1_pre_topc(A_92)) | k5_tmap_1(A_92, B_91)!=u1_pre_topc(A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.86/1.63  tff(c_711, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | k5_tmap_1('#skF_4', '#skF_5')!=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_699])).
% 3.86/1.63  tff(c_720, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | k5_tmap_1('#skF_4', '#skF_5')!=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_711])).
% 3.86/1.63  tff(c_721, plain, (k5_tmap_1('#skF_4', '#skF_5')!=u1_pre_topc('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_152, c_720])).
% 3.86/1.63  tff(c_270, plain, (![A_62, B_63]: (u1_pre_topc(k6_tmap_1(A_62, B_63))=k5_tmap_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.86/1.63  tff(c_282, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_270])).
% 3.86/1.63  tff(c_290, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_282])).
% 3.86/1.63  tff(c_291, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_290])).
% 3.86/1.63  tff(c_42, plain, (![A_6]: (r2_hidden(u1_struct_0(A_6), u1_pre_topc(A_6)) | ~v2_pre_topc(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.86/1.63  tff(c_48, plain, (![A_23]: (m1_subset_1(u1_pre_topc(A_23), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23)))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.86/1.63  tff(c_88, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.86/1.63  tff(c_95, plain, (![A_38, A_23]: (m1_subset_1(A_38, k1_zfmisc_1(u1_struct_0(A_23))) | ~r2_hidden(A_38, u1_pre_topc(A_23)) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_48, c_88])).
% 3.86/1.63  tff(c_546, plain, (![A_81, B_82]: (k5_tmap_1(A_81, B_82)=u1_pre_topc(A_81) | ~r2_hidden(B_82, u1_pre_topc(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.86/1.63  tff(c_593, plain, (![A_85, A_86]: (k5_tmap_1(A_85, A_86)=u1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | ~r2_hidden(A_86, u1_pre_topc(A_85)) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_95, c_546])).
% 3.86/1.63  tff(c_616, plain, (![A_6]: (k5_tmap_1(A_6, u1_struct_0(A_6))=u1_pre_topc(A_6) | v2_struct_0(A_6) | ~v2_pre_topc(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_42, c_593])).
% 3.86/1.63  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.86/1.63  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.86/1.63  tff(c_75, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.86/1.63  tff(c_570, plain, (![A_83, B_84]: (g1_pre_topc(u1_struct_0(A_83), k5_tmap_1(A_83, B_84))=k6_tmap_1(A_83, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.63  tff(c_633, plain, (![A_88]: (g1_pre_topc(u1_struct_0(A_88), k5_tmap_1(A_88, u1_struct_0(A_88)))=k6_tmap_1(A_88, u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_75, c_570])).
% 3.86/1.63  tff(c_945, plain, (![A_107]: (g1_pre_topc(u1_struct_0(A_107), u1_pre_topc(A_107))=k6_tmap_1(A_107, u1_struct_0(A_107)) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107) | v2_struct_0(A_107) | ~v2_pre_topc(A_107) | ~l1_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_616, c_633])).
% 3.86/1.63  tff(c_74, plain, (v3_pre_topc('#skF_5', '#skF_4') | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.63  tff(c_106, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_98, c_74])).
% 3.86/1.63  tff(c_951, plain, (k6_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_945, c_106])).
% 3.86/1.63  tff(c_972, plain, (k6_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_64, c_62, c_951])).
% 3.86/1.63  tff(c_973, plain, (k6_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_972])).
% 3.86/1.63  tff(c_292, plain, (![A_62]: (u1_pre_topc(k6_tmap_1(A_62, u1_struct_0(A_62)))=k5_tmap_1(A_62, u1_struct_0(A_62)) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_75, c_270])).
% 3.86/1.63  tff(c_986, plain, (k5_tmap_1('#skF_4', u1_struct_0('#skF_4'))=u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_973, c_292])).
% 3.86/1.63  tff(c_996, plain, (k5_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k5_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_291, c_986])).
% 3.86/1.63  tff(c_997, plain, (k5_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k5_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_996])).
% 3.86/1.63  tff(c_1012, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_997, c_616])).
% 3.86/1.63  tff(c_1025, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_1012])).
% 3.86/1.63  tff(c_1027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_721, c_1025])).
% 3.86/1.63  tff(c_1028, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=k6_tmap_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 3.86/1.63  tff(c_1029, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.86/1.63  tff(c_1069, plain, (![B_122, A_123]: (r2_hidden(B_122, u1_pre_topc(A_123)) | ~v3_pre_topc(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.86/1.63  tff(c_1075, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1069])).
% 3.86/1.63  tff(c_1083, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1029, c_1075])).
% 3.86/1.63  tff(c_1532, plain, (![A_150, B_151]: (k5_tmap_1(A_150, B_151)=u1_pre_topc(A_150) | ~r2_hidden(B_151, u1_pre_topc(A_150)) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.86/1.63  tff(c_1547, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1532])).
% 3.86/1.63  tff(c_1557, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1083, c_1547])).
% 3.86/1.63  tff(c_1558, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_1557])).
% 3.86/1.63  tff(c_1719, plain, (![A_156, B_157]: (g1_pre_topc(u1_struct_0(A_156), k5_tmap_1(A_156, B_157))=k6_tmap_1(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.63  tff(c_1731, plain, (g1_pre_topc(u1_struct_0('#skF_4'), k5_tmap_1('#skF_4', '#skF_5'))=k6_tmap_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1719])).
% 3.86/1.63  tff(c_1741, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1558, c_1731])).
% 3.86/1.63  tff(c_1743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1028, c_1741])).
% 3.86/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.63  
% 3.86/1.63  Inference rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Ref     : 0
% 3.86/1.63  #Sup     : 426
% 3.86/1.63  #Fact    : 0
% 3.86/1.63  #Define  : 0
% 3.86/1.63  #Split   : 4
% 3.86/1.63  #Chain   : 0
% 3.86/1.63  #Close   : 0
% 3.86/1.63  
% 3.86/1.63  Ordering : KBO
% 3.86/1.63  
% 3.86/1.63  Simplification rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Subsume      : 150
% 3.86/1.63  #Demod        : 266
% 3.86/1.63  #Tautology    : 90
% 3.86/1.63  #SimpNegUnit  : 25
% 3.86/1.63  #BackRed      : 1
% 3.86/1.63  
% 3.86/1.63  #Partial instantiations: 0
% 3.86/1.63  #Strategies tried      : 1
% 3.86/1.63  
% 3.86/1.63  Timing (in seconds)
% 3.86/1.63  ----------------------
% 3.86/1.64  Preprocessing        : 0.33
% 3.86/1.64  Parsing              : 0.17
% 3.86/1.64  CNF conversion       : 0.02
% 3.86/1.64  Main loop            : 0.55
% 3.86/1.64  Inferencing          : 0.19
% 3.86/1.64  Reduction            : 0.19
% 3.86/1.64  Demodulation         : 0.13
% 3.86/1.64  BG Simplification    : 0.03
% 3.86/1.64  Subsumption          : 0.10
% 3.86/1.64  Abstraction          : 0.03
% 3.86/1.64  MUC search           : 0.00
% 3.86/1.64  Cooper               : 0.00
% 3.86/1.64  Total                : 0.92
% 3.86/1.64  Index Insertion      : 0.00
% 3.86/1.64  Index Deletion       : 0.00
% 3.86/1.64  Index Matching       : 0.00
% 3.86/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
