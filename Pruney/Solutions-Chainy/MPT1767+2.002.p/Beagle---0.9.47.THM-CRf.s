%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:15 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  148 (2031 expanded)
%              Number of leaves         :   32 ( 772 expanded)
%              Depth                    :   30
%              Number of atoms          :  581 (15531 expanded)
%              Number of equality atoms :   26 ( 216 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_233,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_95,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_147,axiom,(
    ! [A] :
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
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_194,axiom,(
    ! [A] :
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
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_28,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_76,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( v1_funct_1(k2_tmap_1(A_164,B_165,C_166,D_167))
      | ~ l1_struct_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_164),u1_struct_0(B_165))))
      | ~ v1_funct_2(C_166,u1_struct_0(A_164),u1_struct_0(B_165))
      | ~ v1_funct_1(C_166)
      | ~ l1_struct_0(B_165)
      | ~ l1_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_78,plain,(
    ! [D_167] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167))
      | ~ l1_struct_0(D_167)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_81,plain,(
    ! [D_167] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167))
      | ~ l1_struct_0(D_167)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_78])).

tff(c_82,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_85,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_85])).

tff(c_91,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_90,plain,(
    ! [D_167] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167))
      | ~ l1_struct_0(D_167) ) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_101,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101])).

tff(c_107,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_53,plain,(
    ! [B_162,A_163] :
      ( l1_pre_topc(B_162)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_10,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( m1_subset_1(k2_tmap_1(A_51,B_52,C_53,D_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54),u1_struct_0(B_52))))
      | ~ l1_struct_0(D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_51),u1_struct_0(B_52))))
      | ~ v1_funct_2(C_53,u1_struct_0(A_51),u1_struct_0(B_52))
      | ~ v1_funct_1(C_53)
      | ~ l1_struct_0(B_52)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_148,plain,(
    ! [D_188,B_190,C_191,A_189,E_187] :
      ( k3_tmap_1(A_189,B_190,C_191,D_188,E_187) = k2_partfun1(u1_struct_0(C_191),u1_struct_0(B_190),E_187,u1_struct_0(D_188))
      | ~ m1_pre_topc(D_188,C_191)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_191),u1_struct_0(B_190))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc(D_188,A_189)
      | ~ m1_pre_topc(C_191,A_189)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_916,plain,(
    ! [D_257,A_258,C_256,B_255,A_254,D_259] :
      ( k3_tmap_1(A_258,B_255,D_257,D_259,k2_tmap_1(A_254,B_255,C_256,D_257)) = k2_partfun1(u1_struct_0(D_257),u1_struct_0(B_255),k2_tmap_1(A_254,B_255,C_256,D_257),u1_struct_0(D_259))
      | ~ m1_pre_topc(D_259,D_257)
      | ~ v1_funct_2(k2_tmap_1(A_254,B_255,C_256,D_257),u1_struct_0(D_257),u1_struct_0(B_255))
      | ~ v1_funct_1(k2_tmap_1(A_254,B_255,C_256,D_257))
      | ~ m1_pre_topc(D_259,A_258)
      | ~ m1_pre_topc(D_257,A_258)
      | ~ l1_pre_topc(B_255)
      | ~ v2_pre_topc(B_255)
      | v2_struct_0(B_255)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258)
      | ~ l1_struct_0(D_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_254),u1_struct_0(B_255))))
      | ~ v1_funct_2(C_256,u1_struct_0(A_254),u1_struct_0(B_255))
      | ~ v1_funct_1(C_256)
      | ~ l1_struct_0(B_255)
      | ~ l1_struct_0(A_254) ) ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_922,plain,(
    ! [A_258,D_257,D_259] :
      ( k3_tmap_1(A_258,'#skF_2',D_257,D_259,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257)) = k2_partfun1(u1_struct_0(D_257),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257),u1_struct_0(D_259))
      | ~ m1_pre_topc(D_259,D_257)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257),u1_struct_0(D_257),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257))
      | ~ m1_pre_topc(D_259,A_258)
      | ~ m1_pre_topc(D_257,A_258)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258)
      | ~ l1_struct_0(D_257)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_916])).

tff(c_930,plain,(
    ! [A_258,D_257,D_259] :
      ( k3_tmap_1(A_258,'#skF_2',D_257,D_259,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257)) = k2_partfun1(u1_struct_0(D_257),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257),u1_struct_0(D_259))
      | ~ m1_pre_topc(D_259,D_257)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257),u1_struct_0(D_257),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_257))
      | ~ m1_pre_topc(D_259,A_258)
      | ~ m1_pre_topc(D_257,A_258)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258)
      | ~ l1_struct_0(D_257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_107,c_30,c_28,c_42,c_40,c_922])).

tff(c_951,plain,(
    ! [A_262,D_263,D_264] :
      ( k3_tmap_1(A_262,'#skF_2',D_263,D_264,k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263)) = k2_partfun1(u1_struct_0(D_263),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263),u1_struct_0(D_264))
      | ~ m1_pre_topc(D_264,D_263)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263),u1_struct_0(D_263),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_263))
      | ~ m1_pre_topc(D_264,A_262)
      | ~ m1_pre_topc(D_263,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ l1_struct_0(D_263) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_930])).

tff(c_138,plain,(
    ! [C_183,B_184,D_185,A_186] :
      ( r2_funct_2(u1_struct_0(C_183),u1_struct_0(B_184),D_185,k3_tmap_1(A_186,B_184,C_183,C_183,D_185))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(D_185,u1_struct_0(C_183),u1_struct_0(B_184))
      | ~ v1_funct_1(D_185)
      | ~ m1_pre_topc(C_183,A_186)
      | v2_struct_0(C_183)
      | ~ l1_pre_topc(B_184)
      | ~ v2_pre_topc(B_184)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_143,plain,(
    ! [B_52,A_186,C_53,D_54,A_51] :
      ( r2_funct_2(u1_struct_0(D_54),u1_struct_0(B_52),k2_tmap_1(A_51,B_52,C_53,D_54),k3_tmap_1(A_186,B_52,D_54,D_54,k2_tmap_1(A_51,B_52,C_53,D_54)))
      | ~ v1_funct_2(k2_tmap_1(A_51,B_52,C_53,D_54),u1_struct_0(D_54),u1_struct_0(B_52))
      | ~ v1_funct_1(k2_tmap_1(A_51,B_52,C_53,D_54))
      | ~ m1_pre_topc(D_54,A_186)
      | v2_struct_0(D_54)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ l1_struct_0(D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_51),u1_struct_0(B_52))))
      | ~ v1_funct_2(C_53,u1_struct_0(A_51),u1_struct_0(B_52))
      | ~ v1_funct_1(C_53)
      | ~ l1_struct_0(B_52)
      | ~ l1_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_984,plain,(
    ! [D_264,A_262] :
      ( r2_funct_2(u1_struct_0(D_264),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),k2_partfun1(u1_struct_0(D_264),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),u1_struct_0(D_264)))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),u1_struct_0(D_264),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264))
      | ~ m1_pre_topc(D_264,A_262)
      | v2_struct_0(D_264)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ l1_struct_0(D_264)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_pre_topc(D_264,D_264)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),u1_struct_0(D_264),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264))
      | ~ m1_pre_topc(D_264,A_262)
      | ~ m1_pre_topc(D_264,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ l1_struct_0(D_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_143])).

tff(c_1043,plain,(
    ! [D_264,A_262] :
      ( r2_funct_2(u1_struct_0(D_264),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),k2_partfun1(u1_struct_0(D_264),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),u1_struct_0(D_264)))
      | v2_struct_0(D_264)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_264,D_264)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264),u1_struct_0(D_264),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_264))
      | ~ m1_pre_topc(D_264,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ l1_struct_0(D_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_107,c_30,c_28,c_26,c_42,c_40,c_984])).

tff(c_1355,plain,(
    ! [D_283,A_284] :
      ( r2_funct_2(u1_struct_0(D_283),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_283),k2_partfun1(u1_struct_0(D_283),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_283),u1_struct_0(D_283)))
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(D_283,D_283)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_283),u1_struct_0(D_283),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_283))
      | ~ m1_pre_topc(D_283,A_284)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284)
      | ~ l1_struct_0(D_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1043])).

tff(c_1363,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1355])).

tff(c_1377,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1363])).

tff(c_1378,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_34,c_1377])).

tff(c_1383,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_1386,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_1383])).

tff(c_1390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1386])).

tff(c_1392,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_106,plain,(
    ! [D_167] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167))
      | ~ l1_struct_0(D_167) ) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_16,plain,(
    ! [A_55] :
      ( m1_pre_topc(A_55,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1391,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_1393,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1391])).

tff(c_1396,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1393])).

tff(c_1400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1396])).

tff(c_1401,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1391])).

tff(c_1452,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1401])).

tff(c_1455,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_1452])).

tff(c_1459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_1455])).

tff(c_1461,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_92,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( v1_funct_2(k2_tmap_1(A_168,B_169,C_170,D_171),u1_struct_0(D_171),u1_struct_0(B_169))
      | ~ l1_struct_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_struct_0(B_169)
      | ~ l1_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_94,plain,(
    ! [D_171] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171),u1_struct_0(D_171),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_171)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_97,plain,(
    ! [D_171] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171),u1_struct_0(D_171),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_171)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_30,c_28,c_94])).

tff(c_109,plain,(
    ! [D_171] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171),u1_struct_0(D_171),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_97])).

tff(c_1460,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_1472,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_1475,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_1472])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_1475])).

tff(c_1481,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_152,plain,(
    ! [A_189,D_188] :
      ( k3_tmap_1(A_189,'#skF_2','#skF_1',D_188,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_188))
      | ~ m1_pre_topc(D_188,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_188,A_189)
      | ~ m1_pre_topc('#skF_1',A_189)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_156,plain,(
    ! [A_189,D_188] :
      ( k3_tmap_1(A_189,'#skF_2','#skF_1',D_188,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_188))
      | ~ m1_pre_topc(D_188,'#skF_1')
      | ~ m1_pre_topc(D_188,A_189)
      | ~ m1_pre_topc('#skF_1',A_189)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_152])).

tff(c_159,plain,(
    ! [A_193,D_194] :
      ( k3_tmap_1(A_193,'#skF_2','#skF_1',D_194,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_194))
      | ~ m1_pre_topc(D_194,'#skF_1')
      | ~ m1_pre_topc(D_194,A_193)
      | ~ m1_pre_topc('#skF_1',A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_156])).

tff(c_165,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_159])).

tff(c_175,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_165])).

tff(c_176,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_175])).

tff(c_181,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_185,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_181])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_185])).

tff(c_190,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_119,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k2_partfun1(u1_struct_0(A_178),u1_struct_0(B_179),C_180,u1_struct_0(D_181)) = k2_tmap_1(A_178,B_179,C_180,D_181)
      | ~ m1_pre_topc(D_181,A_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178),u1_struct_0(B_179))))
      | ~ v1_funct_2(C_180,u1_struct_0(A_178),u1_struct_0(B_179))
      | ~ v1_funct_1(C_180)
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | v2_struct_0(B_179)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_123,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_181)
      | ~ m1_pre_topc(D_181,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_127,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_181)
      | ~ m1_pre_topc(D_181,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_30,c_28,c_123])).

tff(c_128,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_181)
      | ~ m1_pre_topc(D_181,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_127])).

tff(c_207,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_128])).

tff(c_214,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_207])).

tff(c_191,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_157,plain,(
    ! [A_189,D_188] :
      ( k3_tmap_1(A_189,'#skF_2','#skF_1',D_188,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_188))
      | ~ m1_pre_topc(D_188,'#skF_1')
      | ~ m1_pre_topc(D_188,A_189)
      | ~ m1_pre_topc('#skF_1',A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_156])).

tff(c_193,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_157])).

tff(c_199,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_191,c_193])).

tff(c_200,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_199])).

tff(c_244,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_128])).

tff(c_251,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_244])).

tff(c_142,plain,(
    ! [A_186] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k3_tmap_1(A_186,'#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_1',A_186)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_146,plain,(
    ! [A_186] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k3_tmap_1(A_186,'#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc('#skF_1',A_186)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_142])).

tff(c_147,plain,(
    ! [A_186] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k3_tmap_1(A_186,'#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc('#skF_1',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_146])).

tff(c_259,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_147])).

tff(c_263,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_191,c_259])).

tff(c_264,plain,(
    r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_263])).

tff(c_20,plain,(
    ! [D_127,B_103,C_119,E_131,A_71,F_133] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0(B_103),k3_tmap_1(A_71,B_103,C_119,D_127,F_133),k2_tmap_1(A_71,B_103,E_131,D_127))
      | ~ m1_pre_topc(D_127,C_119)
      | ~ r2_funct_2(u1_struct_0(C_119),u1_struct_0(B_103),F_133,k2_tmap_1(A_71,B_103,E_131,C_119))
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_119),u1_struct_0(B_103))))
      | ~ v1_funct_2(F_133,u1_struct_0(C_119),u1_struct_0(B_103))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_103))))
      | ~ v1_funct_2(E_131,u1_struct_0(A_71),u1_struct_0(B_103))
      | ~ v1_funct_1(E_131)
      | ~ m1_pre_topc(D_127,A_71)
      | v2_struct_0(D_127)
      | ~ m1_pre_topc(C_119,A_71)
      | v2_struct_0(C_119)
      | ~ l1_pre_topc(B_103)
      | ~ v2_pre_topc(B_103)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_267,plain,(
    ! [D_127] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_127,'#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_127))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_127,'#skF_1')
      | v2_struct_0(D_127)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_264,c_20])).

tff(c_270,plain,(
    ! [D_127] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_127,'#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_127))
      | ~ m1_pre_topc(D_127,'#skF_1')
      | v2_struct_0(D_127)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_191,c_30,c_28,c_26,c_267])).

tff(c_335,plain,(
    ! [D_206] :
      ( r2_funct_2(u1_struct_0(D_206),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_206,'#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_206))
      | ~ m1_pre_topc(D_206,'#skF_1')
      | v2_struct_0(D_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_270])).

tff(c_346,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_335])).

tff(c_358,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_346])).

tff(c_359,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_358])).

tff(c_373,plain,(
    ! [D_127] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_127,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_127))
      | ~ m1_pre_topc(D_127,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_127,'#skF_1')
      | v2_struct_0(D_127)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_359,c_20])).

tff(c_376,plain,(
    ! [D_127] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_127,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_127))
      | ~ m1_pre_topc(D_127,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_127,'#skF_1')
      | v2_struct_0(D_127)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_32,c_30,c_28,c_26,c_373])).

tff(c_377,plain,(
    ! [D_127] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_127,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_127))
      | ~ m1_pre_topc(D_127,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_127,'#skF_1')
      | v2_struct_0(D_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_34,c_376])).

tff(c_1595,plain,(
    ! [D_127] :
      ( r2_funct_2(u1_struct_0(D_127),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_127,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_127))
      | ~ m1_pre_topc(D_127,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_127,'#skF_1')
      | v2_struct_0(D_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1481,c_377])).

tff(c_1596,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1595])).

tff(c_1599,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1596])).

tff(c_1603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_107,c_30,c_28,c_26,c_1392,c_1599])).

tff(c_1657,plain,(
    ! [D_309] :
      ( r2_funct_2(u1_struct_0(D_309),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_309,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_309))
      | ~ m1_pre_topc(D_309,'#skF_4')
      | ~ m1_pre_topc(D_309,'#skF_1')
      | v2_struct_0(D_309) ) ),
    inference(splitRight,[status(thm)],[c_1595])).

tff(c_22,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_1662,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1657,c_22])).

tff(c_1669,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24,c_1662])).

tff(c_1671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.93  
% 4.78/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.93  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.78/1.93  
% 4.78/1.93  %Foreground sorts:
% 4.78/1.93  
% 4.78/1.93  
% 4.78/1.93  %Background operators:
% 4.78/1.93  
% 4.78/1.93  
% 4.78/1.93  %Foreground operators:
% 4.78/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.78/1.93  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.78/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.78/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.78/1.93  tff('#skF_5', type, '#skF_5': $i).
% 4.78/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.78/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.78/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.78/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.78/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.78/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.78/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.78/1.93  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.78/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.78/1.93  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.78/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.78/1.93  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.78/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.93  
% 5.18/1.96  tff(f_233, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 5.18/1.96  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.18/1.96  tff(f_113, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 5.18/1.96  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.18/1.96  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.18/1.96  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 5.18/1.96  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.18/1.96  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.18/1.96  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tmap_1)).
% 5.18/1.96  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.18/1.96  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_28, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_76, plain, (![A_164, B_165, C_166, D_167]: (v1_funct_1(k2_tmap_1(A_164, B_165, C_166, D_167)) | ~l1_struct_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_164), u1_struct_0(B_165)))) | ~v1_funct_2(C_166, u1_struct_0(A_164), u1_struct_0(B_165)) | ~v1_funct_1(C_166) | ~l1_struct_0(B_165) | ~l1_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.18/1.96  tff(c_78, plain, (![D_167]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167)) | ~l1_struct_0(D_167) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_76])).
% 5.18/1.96  tff(c_81, plain, (![D_167]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167)) | ~l1_struct_0(D_167) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_78])).
% 5.18/1.96  tff(c_82, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_81])).
% 5.18/1.96  tff(c_85, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_82])).
% 5.18/1.96  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_85])).
% 5.18/1.96  tff(c_91, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_81])).
% 5.18/1.96  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_90, plain, (![D_167]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167)) | ~l1_struct_0(D_167))), inference(splitRight, [status(thm)], [c_81])).
% 5.18/1.96  tff(c_98, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_90])).
% 5.18/1.96  tff(c_101, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_98])).
% 5.18/1.96  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_101])).
% 5.18/1.96  tff(c_107, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_90])).
% 5.18/1.96  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_53, plain, (![B_162, A_163]: (l1_pre_topc(B_162) | ~m1_pre_topc(B_162, A_163) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.18/1.96  tff(c_62, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_53])).
% 5.18/1.96  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 5.18/1.96  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_10, plain, (![A_51, B_52, C_53, D_54]: (m1_subset_1(k2_tmap_1(A_51, B_52, C_53, D_54), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54), u1_struct_0(B_52)))) | ~l1_struct_0(D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_51), u1_struct_0(B_52)))) | ~v1_funct_2(C_53, u1_struct_0(A_51), u1_struct_0(B_52)) | ~v1_funct_1(C_53) | ~l1_struct_0(B_52) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.18/1.96  tff(c_148, plain, (![D_188, B_190, C_191, A_189, E_187]: (k3_tmap_1(A_189, B_190, C_191, D_188, E_187)=k2_partfun1(u1_struct_0(C_191), u1_struct_0(B_190), E_187, u1_struct_0(D_188)) | ~m1_pre_topc(D_188, C_191) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191), u1_struct_0(B_190)))) | ~v1_funct_2(E_187, u1_struct_0(C_191), u1_struct_0(B_190)) | ~v1_funct_1(E_187) | ~m1_pre_topc(D_188, A_189) | ~m1_pre_topc(C_191, A_189) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.18/1.96  tff(c_916, plain, (![D_257, A_258, C_256, B_255, A_254, D_259]: (k3_tmap_1(A_258, B_255, D_257, D_259, k2_tmap_1(A_254, B_255, C_256, D_257))=k2_partfun1(u1_struct_0(D_257), u1_struct_0(B_255), k2_tmap_1(A_254, B_255, C_256, D_257), u1_struct_0(D_259)) | ~m1_pre_topc(D_259, D_257) | ~v1_funct_2(k2_tmap_1(A_254, B_255, C_256, D_257), u1_struct_0(D_257), u1_struct_0(B_255)) | ~v1_funct_1(k2_tmap_1(A_254, B_255, C_256, D_257)) | ~m1_pre_topc(D_259, A_258) | ~m1_pre_topc(D_257, A_258) | ~l1_pre_topc(B_255) | ~v2_pre_topc(B_255) | v2_struct_0(B_255) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258) | ~l1_struct_0(D_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_254), u1_struct_0(B_255)))) | ~v1_funct_2(C_256, u1_struct_0(A_254), u1_struct_0(B_255)) | ~v1_funct_1(C_256) | ~l1_struct_0(B_255) | ~l1_struct_0(A_254))), inference(resolution, [status(thm)], [c_10, c_148])).
% 5.18/1.96  tff(c_922, plain, (![A_258, D_257, D_259]: (k3_tmap_1(A_258, '#skF_2', D_257, D_259, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257))=k2_partfun1(u1_struct_0(D_257), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257), u1_struct_0(D_259)) | ~m1_pre_topc(D_259, D_257) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257), u1_struct_0(D_257), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257)) | ~m1_pre_topc(D_259, A_258) | ~m1_pre_topc(D_257, A_258) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258) | ~l1_struct_0(D_257) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_916])).
% 5.18/1.96  tff(c_930, plain, (![A_258, D_257, D_259]: (k3_tmap_1(A_258, '#skF_2', D_257, D_259, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257))=k2_partfun1(u1_struct_0(D_257), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257), u1_struct_0(D_259)) | ~m1_pre_topc(D_259, D_257) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257), u1_struct_0(D_257), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_257)) | ~m1_pre_topc(D_259, A_258) | ~m1_pre_topc(D_257, A_258) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258) | ~l1_struct_0(D_257))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_107, c_30, c_28, c_42, c_40, c_922])).
% 5.18/1.96  tff(c_951, plain, (![A_262, D_263, D_264]: (k3_tmap_1(A_262, '#skF_2', D_263, D_264, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263))=k2_partfun1(u1_struct_0(D_263), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263), u1_struct_0(D_264)) | ~m1_pre_topc(D_264, D_263) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263), u1_struct_0(D_263), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_263)) | ~m1_pre_topc(D_264, A_262) | ~m1_pre_topc(D_263, A_262) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262) | ~l1_struct_0(D_263))), inference(negUnitSimplification, [status(thm)], [c_44, c_930])).
% 5.18/1.96  tff(c_138, plain, (![C_183, B_184, D_185, A_186]: (r2_funct_2(u1_struct_0(C_183), u1_struct_0(B_184), D_185, k3_tmap_1(A_186, B_184, C_183, C_183, D_185)) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183), u1_struct_0(B_184)))) | ~v1_funct_2(D_185, u1_struct_0(C_183), u1_struct_0(B_184)) | ~v1_funct_1(D_185) | ~m1_pre_topc(C_183, A_186) | v2_struct_0(C_183) | ~l1_pre_topc(B_184) | ~v2_pre_topc(B_184) | v2_struct_0(B_184) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.18/1.96  tff(c_143, plain, (![B_52, A_186, C_53, D_54, A_51]: (r2_funct_2(u1_struct_0(D_54), u1_struct_0(B_52), k2_tmap_1(A_51, B_52, C_53, D_54), k3_tmap_1(A_186, B_52, D_54, D_54, k2_tmap_1(A_51, B_52, C_53, D_54))) | ~v1_funct_2(k2_tmap_1(A_51, B_52, C_53, D_54), u1_struct_0(D_54), u1_struct_0(B_52)) | ~v1_funct_1(k2_tmap_1(A_51, B_52, C_53, D_54)) | ~m1_pre_topc(D_54, A_186) | v2_struct_0(D_54) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~l1_struct_0(D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_51), u1_struct_0(B_52)))) | ~v1_funct_2(C_53, u1_struct_0(A_51), u1_struct_0(B_52)) | ~v1_funct_1(C_53) | ~l1_struct_0(B_52) | ~l1_struct_0(A_51))), inference(resolution, [status(thm)], [c_10, c_138])).
% 5.18/1.96  tff(c_984, plain, (![D_264, A_262]: (r2_funct_2(u1_struct_0(D_264), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), k2_partfun1(u1_struct_0(D_264), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), u1_struct_0(D_264))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), u1_struct_0(D_264), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264)) | ~m1_pre_topc(D_264, A_262) | v2_struct_0(D_264) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262) | ~l1_struct_0(D_264) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~m1_pre_topc(D_264, D_264) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), u1_struct_0(D_264), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264)) | ~m1_pre_topc(D_264, A_262) | ~m1_pre_topc(D_264, A_262) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262) | ~l1_struct_0(D_264))), inference(superposition, [status(thm), theory('equality')], [c_951, c_143])).
% 5.18/1.96  tff(c_1043, plain, (![D_264, A_262]: (r2_funct_2(u1_struct_0(D_264), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), k2_partfun1(u1_struct_0(D_264), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), u1_struct_0(D_264))) | v2_struct_0(D_264) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_264, D_264) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264), u1_struct_0(D_264), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_264)) | ~m1_pre_topc(D_264, A_262) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262) | ~l1_struct_0(D_264))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_107, c_30, c_28, c_26, c_42, c_40, c_984])).
% 5.18/1.96  tff(c_1355, plain, (![D_283, A_284]: (r2_funct_2(u1_struct_0(D_283), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_283), k2_partfun1(u1_struct_0(D_283), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_283), u1_struct_0(D_283))) | v2_struct_0(D_283) | ~m1_pre_topc(D_283, D_283) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_283), u1_struct_0(D_283), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_283)) | ~m1_pre_topc(D_283, A_284) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284) | ~l1_struct_0(D_283))), inference(negUnitSimplification, [status(thm)], [c_44, c_1043])).
% 5.18/1.96  tff(c_1363, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1355])).
% 5.18/1.96  tff(c_1377, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1363])).
% 5.18/1.96  tff(c_1378, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_34, c_1377])).
% 5.18/1.96  tff(c_1383, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1378])).
% 5.18/1.96  tff(c_1386, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2, c_1383])).
% 5.18/1.96  tff(c_1390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1386])).
% 5.18/1.96  tff(c_1392, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1378])).
% 5.18/1.96  tff(c_106, plain, (![D_167]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167)) | ~l1_struct_0(D_167))), inference(splitRight, [status(thm)], [c_90])).
% 5.18/1.96  tff(c_16, plain, (![A_55]: (m1_pre_topc(A_55, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.18/1.96  tff(c_1391, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1378])).
% 5.18/1.96  tff(c_1393, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1391])).
% 5.18/1.96  tff(c_1396, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1393])).
% 5.18/1.96  tff(c_1400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1396])).
% 5.18/1.96  tff(c_1401, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1391])).
% 5.18/1.96  tff(c_1452, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1401])).
% 5.18/1.96  tff(c_1455, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_106, c_1452])).
% 5.18/1.96  tff(c_1459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1392, c_1455])).
% 5.18/1.96  tff(c_1461, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_1401])).
% 5.18/1.96  tff(c_92, plain, (![A_168, B_169, C_170, D_171]: (v1_funct_2(k2_tmap_1(A_168, B_169, C_170, D_171), u1_struct_0(D_171), u1_struct_0(B_169)) | ~l1_struct_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168), u1_struct_0(B_169)))) | ~v1_funct_2(C_170, u1_struct_0(A_168), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~l1_struct_0(B_169) | ~l1_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.18/1.96  tff(c_94, plain, (![D_171]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171), u1_struct_0(D_171), u1_struct_0('#skF_2')) | ~l1_struct_0(D_171) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_92])).
% 5.18/1.96  tff(c_97, plain, (![D_171]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171), u1_struct_0(D_171), u1_struct_0('#skF_2')) | ~l1_struct_0(D_171) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_30, c_28, c_94])).
% 5.18/1.96  tff(c_109, plain, (![D_171]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171), u1_struct_0(D_171), u1_struct_0('#skF_2')) | ~l1_struct_0(D_171))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_97])).
% 5.18/1.96  tff(c_1460, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1401])).
% 5.18/1.96  tff(c_1472, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1460])).
% 5.18/1.96  tff(c_1475, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_109, c_1472])).
% 5.18/1.96  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1392, c_1475])).
% 5.18/1.96  tff(c_1481, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1460])).
% 5.18/1.96  tff(c_152, plain, (![A_189, D_188]: (k3_tmap_1(A_189, '#skF_2', '#skF_1', D_188, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_188)) | ~m1_pre_topc(D_188, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_188, A_189) | ~m1_pre_topc('#skF_1', A_189) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_26, c_148])).
% 5.18/1.96  tff(c_156, plain, (![A_189, D_188]: (k3_tmap_1(A_189, '#skF_2', '#skF_1', D_188, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_188)) | ~m1_pre_topc(D_188, '#skF_1') | ~m1_pre_topc(D_188, A_189) | ~m1_pre_topc('#skF_1', A_189) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_152])).
% 5.18/1.96  tff(c_159, plain, (![A_193, D_194]: (k3_tmap_1(A_193, '#skF_2', '#skF_1', D_194, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_194)) | ~m1_pre_topc(D_194, '#skF_1') | ~m1_pre_topc(D_194, A_193) | ~m1_pre_topc('#skF_1', A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(negUnitSimplification, [status(thm)], [c_44, c_156])).
% 5.18/1.96  tff(c_165, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_159])).
% 5.18/1.96  tff(c_175, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_165])).
% 5.18/1.96  tff(c_176, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_175])).
% 5.18/1.96  tff(c_181, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_176])).
% 5.18/1.96  tff(c_185, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_181])).
% 5.18/1.96  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_185])).
% 5.18/1.96  tff(c_190, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_176])).
% 5.18/1.96  tff(c_119, plain, (![A_178, B_179, C_180, D_181]: (k2_partfun1(u1_struct_0(A_178), u1_struct_0(B_179), C_180, u1_struct_0(D_181))=k2_tmap_1(A_178, B_179, C_180, D_181) | ~m1_pre_topc(D_181, A_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178), u1_struct_0(B_179)))) | ~v1_funct_2(C_180, u1_struct_0(A_178), u1_struct_0(B_179)) | ~v1_funct_1(C_180) | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | v2_struct_0(B_179) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.18/1.96  tff(c_123, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_181) | ~m1_pre_topc(D_181, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_119])).
% 5.18/1.96  tff(c_127, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_181) | ~m1_pre_topc(D_181, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_30, c_28, c_123])).
% 5.18/1.96  tff(c_128, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_181) | ~m1_pre_topc(D_181, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_127])).
% 5.18/1.96  tff(c_207, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_190, c_128])).
% 5.18/1.96  tff(c_214, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_207])).
% 5.18/1.96  tff(c_191, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_176])).
% 5.18/1.96  tff(c_157, plain, (![A_189, D_188]: (k3_tmap_1(A_189, '#skF_2', '#skF_1', D_188, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_188)) | ~m1_pre_topc(D_188, '#skF_1') | ~m1_pre_topc(D_188, A_189) | ~m1_pre_topc('#skF_1', A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(negUnitSimplification, [status(thm)], [c_44, c_156])).
% 5.18/1.96  tff(c_193, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_191, c_157])).
% 5.18/1.96  tff(c_199, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_191, c_193])).
% 5.18/1.96  tff(c_200, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_199])).
% 5.18/1.96  tff(c_244, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_200, c_128])).
% 5.18/1.96  tff(c_251, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_244])).
% 5.18/1.96  tff(c_142, plain, (![A_186]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k3_tmap_1(A_186, '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_1', A_186) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_26, c_138])).
% 5.18/1.96  tff(c_146, plain, (![A_186]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k3_tmap_1(A_186, '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc('#skF_1', A_186) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_142])).
% 5.18/1.96  tff(c_147, plain, (![A_186]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k3_tmap_1(A_186, '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc('#skF_1', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_146])).
% 5.18/1.96  tff(c_259, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_251, c_147])).
% 5.18/1.96  tff(c_263, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_191, c_259])).
% 5.18/1.96  tff(c_264, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_263])).
% 5.18/1.96  tff(c_20, plain, (![D_127, B_103, C_119, E_131, A_71, F_133]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0(B_103), k3_tmap_1(A_71, B_103, C_119, D_127, F_133), k2_tmap_1(A_71, B_103, E_131, D_127)) | ~m1_pre_topc(D_127, C_119) | ~r2_funct_2(u1_struct_0(C_119), u1_struct_0(B_103), F_133, k2_tmap_1(A_71, B_103, E_131, C_119)) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_119), u1_struct_0(B_103)))) | ~v1_funct_2(F_133, u1_struct_0(C_119), u1_struct_0(B_103)) | ~v1_funct_1(F_133) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_103)))) | ~v1_funct_2(E_131, u1_struct_0(A_71), u1_struct_0(B_103)) | ~v1_funct_1(E_131) | ~m1_pre_topc(D_127, A_71) | v2_struct_0(D_127) | ~m1_pre_topc(C_119, A_71) | v2_struct_0(C_119) | ~l1_pre_topc(B_103) | ~v2_pre_topc(B_103) | v2_struct_0(B_103) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_194])).
% 5.18/1.96  tff(c_267, plain, (![D_127]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_127, '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_127)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_127, '#skF_1') | v2_struct_0(D_127) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_264, c_20])).
% 5.18/1.96  tff(c_270, plain, (![D_127]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_127, '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_127)) | ~m1_pre_topc(D_127, '#skF_1') | v2_struct_0(D_127) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_191, c_30, c_28, c_26, c_267])).
% 5.18/1.96  tff(c_335, plain, (![D_206]: (r2_funct_2(u1_struct_0(D_206), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_206, '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_206)) | ~m1_pre_topc(D_206, '#skF_1') | v2_struct_0(D_206))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_270])).
% 5.18/1.96  tff(c_346, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_214, c_335])).
% 5.18/1.96  tff(c_358, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_346])).
% 5.18/1.96  tff(c_359, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_358])).
% 5.18/1.96  tff(c_373, plain, (![D_127]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_127, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_127)) | ~m1_pre_topc(D_127, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_127, '#skF_1') | v2_struct_0(D_127) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_359, c_20])).
% 5.18/1.96  tff(c_376, plain, (![D_127]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_127, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_127)) | ~m1_pre_topc(D_127, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_127, '#skF_1') | v2_struct_0(D_127) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_32, c_30, c_28, c_26, c_373])).
% 5.18/1.96  tff(c_377, plain, (![D_127]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_127, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_127)) | ~m1_pre_topc(D_127, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_127, '#skF_1') | v2_struct_0(D_127))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_34, c_376])).
% 5.18/1.96  tff(c_1595, plain, (![D_127]: (r2_funct_2(u1_struct_0(D_127), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_127, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_127)) | ~m1_pre_topc(D_127, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_127, '#skF_1') | v2_struct_0(D_127))), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1481, c_377])).
% 5.18/1.96  tff(c_1596, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1595])).
% 5.18/1.96  tff(c_1599, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_1596])).
% 5.18/1.96  tff(c_1603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_107, c_30, c_28, c_26, c_1392, c_1599])).
% 5.18/1.96  tff(c_1657, plain, (![D_309]: (r2_funct_2(u1_struct_0(D_309), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_309, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_309)) | ~m1_pre_topc(D_309, '#skF_4') | ~m1_pre_topc(D_309, '#skF_1') | v2_struct_0(D_309))), inference(splitRight, [status(thm)], [c_1595])).
% 5.18/1.96  tff(c_22, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 5.18/1.96  tff(c_1662, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1657, c_22])).
% 5.18/1.96  tff(c_1669, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24, c_1662])).
% 5.18/1.96  tff(c_1671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1669])).
% 5.18/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.96  
% 5.18/1.96  Inference rules
% 5.18/1.96  ----------------------
% 5.18/1.96  #Ref     : 0
% 5.18/1.96  #Sup     : 298
% 5.18/1.96  #Fact    : 0
% 5.18/1.96  #Define  : 0
% 5.18/1.96  #Split   : 19
% 5.18/1.96  #Chain   : 0
% 5.18/1.96  #Close   : 0
% 5.18/1.96  
% 5.18/1.96  Ordering : KBO
% 5.18/1.96  
% 5.18/1.96  Simplification rules
% 5.18/1.96  ----------------------
% 5.18/1.96  #Subsume      : 85
% 5.18/1.96  #Demod        : 783
% 5.18/1.96  #Tautology    : 83
% 5.18/1.96  #SimpNegUnit  : 98
% 5.18/1.96  #BackRed      : 3
% 5.18/1.96  
% 5.18/1.96  #Partial instantiations: 0
% 5.18/1.96  #Strategies tried      : 1
% 5.18/1.96  
% 5.18/1.96  Timing (in seconds)
% 5.18/1.96  ----------------------
% 5.18/1.96  Preprocessing        : 0.35
% 5.18/1.96  Parsing              : 0.18
% 5.18/1.96  CNF conversion       : 0.04
% 5.18/1.96  Main loop            : 0.78
% 5.18/1.96  Inferencing          : 0.27
% 5.18/1.96  Reduction            : 0.28
% 5.18/1.96  Demodulation         : 0.21
% 5.18/1.96  BG Simplification    : 0.03
% 5.18/1.96  Subsumption          : 0.16
% 5.18/1.96  Abstraction          : 0.04
% 5.18/1.96  MUC search           : 0.00
% 5.18/1.96  Cooper               : 0.00
% 5.18/1.96  Total                : 1.18
% 5.18/1.96  Index Insertion      : 0.00
% 5.18/1.96  Index Deletion       : 0.00
% 5.18/1.96  Index Matching       : 0.00
% 5.18/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
