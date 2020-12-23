%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1762+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:21 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 907 expanded)
%              Number of leaves         :   37 ( 344 expanded)
%              Depth                    :   19
%              Number of atoms          :  398 (8557 expanded)
%              Number of equality atoms :   43 ( 603 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => ( ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(D))
                                   => ( r2_hidden(G,u1_struct_0(C))
                                     => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,G) = k1_funct_1(F,G) ) )
                               => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tmap_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_130,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_36,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_34,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_117,plain,(
    ! [A_251,B_252,D_253] :
      ( r2_funct_2(A_251,B_252,D_253,D_253)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_funct_2(D_253,A_251,B_252)
      | ~ v1_funct_1(D_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_119,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_8','#skF_8')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_127,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_119])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_46,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_67,plain,(
    ! [B_236,A_237] :
      ( l1_pre_topc(B_236)
      | ~ m1_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_73,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_67])).

tff(c_80,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_73])).

tff(c_4,plain,(
    ! [A_32] :
      ( l1_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_162,plain,(
    ! [D_268,B_267,A_266,C_264,E_265] :
      ( m1_subset_1('#skF_2'(C_264,E_265,A_266,B_267,D_268),A_266)
      | k2_partfun1(A_266,B_267,C_264,D_268) = E_265
      | ~ m1_subset_1(E_265,k1_zfmisc_1(k2_zfmisc_1(D_268,B_267)))
      | ~ v1_funct_2(E_265,D_268,B_267)
      | ~ v1_funct_1(E_265)
      | ~ m1_subset_1(D_268,k1_zfmisc_1(A_266))
      | v1_xboole_0(D_268)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267)))
      | ~ v1_funct_2(C_264,A_266,B_267)
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(B_267)
      | v1_xboole_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_164,plain,(
    ! [C_264,A_266] :
      ( m1_subset_1('#skF_2'(C_264,'#skF_8',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_266))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_172,plain,(
    ! [C_264,A_266] :
      ( m1_subset_1('#skF_2'(C_264,'#skF_8',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_266))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_164])).

tff(c_177,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_10,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(u1_struct_0(A_38))
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_182,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_10])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_182])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_188])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_206])).

tff(c_212,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_42,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_166,plain,(
    ! [C_264,A_266] :
      ( m1_subset_1('#skF_2'(C_264,'#skF_7',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_6')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_6')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_266))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_266) ) ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_175,plain,(
    ! [C_264,A_266] :
      ( m1_subset_1('#skF_2'(C_264,'#skF_7',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_6')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_6')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_266))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_166])).

tff(c_249,plain,(
    ! [C_264,A_266] :
      ( m1_subset_1('#skF_2'(C_264,'#skF_7',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_6')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_6')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(A_266))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(A_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_175])).

tff(c_250,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_276,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_250,c_10])).

tff(c_282,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_276])).

tff(c_285,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_282])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_285])).

tff(c_291,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_22,plain,(
    ! [B_107,A_105] :
      ( m1_subset_1(u1_struct_0(B_107),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_107,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_83,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_211,plain,(
    ! [C_264,A_266] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_2'(C_264,'#skF_8',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_266))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(A_266) ) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_213,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_220,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_213,c_10])).

tff(c_226,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_220])).

tff(c_229,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_226])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_229])).

tff(c_235,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_344,plain,(
    ! [C_299,E_302,B_300,A_301,D_298] :
      ( k3_tmap_1(A_301,B_300,C_299,D_298,E_302) = k2_partfun1(u1_struct_0(C_299),u1_struct_0(B_300),E_302,u1_struct_0(D_298))
      | ~ m1_pre_topc(D_298,C_299)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299),u1_struct_0(B_300))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_299),u1_struct_0(B_300))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc(D_298,A_301)
      | ~ m1_pre_topc(C_299,A_301)
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | v2_struct_0(B_300)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_354,plain,(
    ! [A_301,D_298] :
      ( k3_tmap_1(A_301,'#skF_4','#skF_6',D_298,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0(D_298))
      | ~ m1_pre_topc(D_298,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_298,A_301)
      | ~ m1_pre_topc('#skF_6',A_301)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_40,c_344])).

tff(c_366,plain,(
    ! [A_301,D_298] :
      ( k3_tmap_1(A_301,'#skF_4','#skF_6',D_298,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0(D_298))
      | ~ m1_pre_topc(D_298,'#skF_6')
      | ~ m1_pre_topc(D_298,A_301)
      | ~ m1_pre_topc('#skF_6',A_301)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_354])).

tff(c_390,plain,(
    ! [A_305,D_306] :
      ( k3_tmap_1(A_305,'#skF_4','#skF_6',D_306,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0(D_306))
      | ~ m1_pre_topc(D_306,'#skF_6')
      | ~ m1_pre_topc(D_306,A_305)
      | ~ m1_pre_topc('#skF_6',A_305)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_366])).

tff(c_396,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_390])).

tff(c_407,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_38,c_396])).

tff(c_408,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_407])).

tff(c_317,plain,(
    ! [E_290,B_292,A_291,C_289,D_293] :
      ( r2_hidden('#skF_2'(C_289,E_290,A_291,B_292,D_293),D_293)
      | k2_partfun1(A_291,B_292,C_289,D_293) = E_290
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(D_293,B_292)))
      | ~ v1_funct_2(E_290,D_293,B_292)
      | ~ v1_funct_1(E_290)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(A_291))
      | v1_xboole_0(D_293)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_2(C_289,A_291,B_292)
      | ~ v1_funct_1(C_289)
      | v1_xboole_0(B_292)
      | v1_xboole_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_325,plain,(
    ! [C_289,A_291] :
      ( r2_hidden('#skF_2'(C_289,'#skF_8',A_291,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_291,u1_struct_0('#skF_4'),C_289,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_291))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_291,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_289,A_291,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_289)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_32,c_317])).

tff(c_335,plain,(
    ! [C_289,A_291] :
      ( r2_hidden('#skF_2'(C_289,'#skF_8',A_291,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_291,u1_struct_0('#skF_4'),C_289,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_291))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_291,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_289,A_291,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_289)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_325])).

tff(c_336,plain,(
    ! [C_289,A_291] :
      ( r2_hidden('#skF_2'(C_289,'#skF_8',A_291,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_291,u1_struct_0('#skF_4'),C_289,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_291))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_291,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_289,A_291,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_289)
      | v1_xboole_0(A_291) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_235,c_335])).

tff(c_30,plain,(
    ! [G_233] :
      ( k3_funct_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',G_233) = k1_funct_1('#skF_8',G_233)
      | ~ r2_hidden(G_233,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(G_233,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_414,plain,(
    ! [E_308,C_307,D_311,B_310,A_309] :
      ( k3_funct_2(A_309,B_310,C_307,'#skF_2'(C_307,E_308,A_309,B_310,D_311)) != k1_funct_1(E_308,'#skF_2'(C_307,E_308,A_309,B_310,D_311))
      | k2_partfun1(A_309,B_310,C_307,D_311) = E_308
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(D_311,B_310)))
      | ~ v1_funct_2(E_308,D_311,B_310)
      | ~ v1_funct_1(E_308)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(A_309))
      | v1_xboole_0(D_311)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_2(C_307,A_309,B_310)
      | ~ v1_funct_1(C_307)
      | v1_xboole_0(B_310)
      | v1_xboole_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_417,plain,(
    ! [E_308,D_311] :
      ( k1_funct_1(E_308,'#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311)) != k1_funct_1('#skF_8','#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311))
      | k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_311) = E_308
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(D_311,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_308,D_311,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_308)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v1_xboole_0(D_311)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_414])).

tff(c_419,plain,(
    ! [E_308,D_311] :
      ( k1_funct_1(E_308,'#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311)) != k1_funct_1('#skF_8','#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311))
      | k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_311) = E_308
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(D_311,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_308,D_311,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_308)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v1_xboole_0(D_311)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_417])).

tff(c_420,plain,(
    ! [E_308,D_311] :
      ( k1_funct_1(E_308,'#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311)) != k1_funct_1('#skF_8','#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311))
      | k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_311) = E_308
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(D_311,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(E_308,D_311,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(E_308)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v1_xboole_0(D_311)
      | ~ r2_hidden('#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_7',E_308,u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_212,c_419])).

tff(c_437,plain,(
    ! [D_311] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_311) = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(D_311,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_8',D_311,u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(D_311,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v1_xboole_0(D_311)
      | ~ r2_hidden('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_311),u1_struct_0('#skF_6')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_420])).

tff(c_441,plain,(
    ! [D_317] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',D_317) = '#skF_8'
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(D_317,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_8',D_317,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v1_xboole_0(D_317)
      | ~ r2_hidden('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_317),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),D_317),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_437])).

tff(c_445,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_6'))
    | k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0('#skF_5')) = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_336,c_441])).

tff(c_451,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_6'))
    | k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_408,c_34,c_32,c_445])).

tff(c_452,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_6'))
    | k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_235,c_451])).

tff(c_456,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_459,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_456])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_38,c_459])).

tff(c_465,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_234,plain,(
    ! [C_264,A_266] :
      ( m1_subset_1('#skF_2'(C_264,'#skF_8',A_266,u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),A_266)
      | k2_partfun1(A_266,u1_struct_0('#skF_4'),C_264,u1_struct_0('#skF_5')) = '#skF_8'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_266))
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_266,u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_264,A_266,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_264)
      | v1_xboole_0(A_266) ) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_464,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_6'))
    | k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_469,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_497,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7',u1_struct_0('#skF_5')) = '#skF_8'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_234,c_469])).

tff(c_500,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_465,c_408,c_497])).

tff(c_501,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_500])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_503,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_28])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_503])).

tff(c_507,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_510,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_28])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_510])).

%------------------------------------------------------------------------------
